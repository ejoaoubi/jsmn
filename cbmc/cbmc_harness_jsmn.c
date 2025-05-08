/*
    João Pedro Esteves, nº M14605
    Mestrado em Eng.Informática
    Segurança e Fiabilidade de Software

*/

/*
    JSMN:

    - Parser JSON minimalista, em um único arquivo de cabeçalho (jsmn.h).
    - Não aloca memória dinamicamente (o usuário fornece o buffer de tokens).
    - API principal: jsmn_init() e jsmn_parse().
    - jsmn_parse() preenche um array de jsmntok_t fornecido pelo usuário com informações sobre os tokens JSON encontrados (tipo, início, fim, tamanho/número de filhos).
    - Retorna o número de tokens usados ou um código de erro (JSMN_ERROR_INVAL, JSMN_ERROR_NOMEM, JSMN_ERROR_PART).

*/

#include <stdio.h>
#include <string.h>                    
#include <assert.h>
   
#include "jsmn.h"                                                                                                                                  

// --- Limites para a verificação ---
// Estes valores afetam o tempo de análise do CBMC. Comece com valores pequenos.
#define MAX_JSON_STRING_LEN 8 // Comprimento máximo da string JSON de entrada
#define MAX_TOKENS_ARRAY_SIZE 4 // Tamanho máximo do array de tokens

// --- Símbolos não determinísticos do CBMC ---
// Estas funções são "mágicas" para o CBMC e representam entradas arbitrárias.
// Você pode precisar declarar os protótipos se o seu CBMC não os trouxer automaticamente.
// Geralmente, <cprover/cprover.h> os teria, mas para CBMC básico, ele os reconhece.
// Para garantir, podemos adicioná-los (ou equivalentes):
extern void __CPROVER_assume(int assumption);
// extern size_t nondet_sizet(); // Para size_t não determinístico
// extern unsigned int nondet_uint(); // Para unsigned int não determinístico
// extern char nondet_char(); // Para char não determinístico

// Se as funções nondet_* não estiverem disponíveis no seu CBMC diretamente,
// você pode criar variáveis e não inicializá-las; CBMC as tratará como não determinísticas.
// Ou use __CPROVER_input("nome", var);

int main_harness() {
    jsmn_parser parser;
    jsmntok_t tokens[MAX_TOKENS_ARRAY_SIZE];

    // 1. Entradas não determinísticas
    char json_input_string[MAX_JSON_STRING_LEN];
    size_t json_len;
    unsigned int num_tokens_available;

    // __CPROVER_input("json_len_input", json_len); // Outra forma de declarar entrada
    // __CPROVER_input("num_tokens_input", num_tokens_available);
    // Para o array de char, o CBMC já o trata como não determinístico se não for inicializado
    // ou podemos fazer char por char, mas é mais complexo.
    // Deixar não inicializado é a forma mais simples para o CBMC explorar.

    // 2. Restrições (Assumptions) sobre as entradas
    // json_len deve estar dentro dos limites do buffer e ser razoável
    __CPROVER_assume(json_len < MAX_JSON_STRING_LEN); // Evita ler fora de json_input_string
                                                     // json_len pode ser 0 (string vazia)

    // num_tokens_available deve estar dentro dos limites do array de tokens
    __CPROVER_assume(num_tokens_available <= MAX_TOKENS_ARRAY_SIZE);
    // num_tokens_available pode ser 0

    // Se quisermos garantir que a string é null-terminated para o CBMC,
    // embora jsmn_parse use json_len e não dependa da terminação nula:
    // if (json_len < MAX_JSON_STRING_LEN) {
    //     json_input_string[json_len] = '\0';
    // }

    // 3. Inicializar o parser JSMN
    jsmn_init(&parser);

    // 4. Chamar a função principal a ser testada
    // JSMN permite que 'tokens' seja NULL para apenas contar os tokens necessários.
    // Vamos testar os dois casos.
    unsigned char nondet_choice_tokens_null; // 0 ou 1
    __CPROVER_assume(nondet_choice_tokens_null == 0 || nondet_choice_tokens_null == 1);

    jsmntok_t *tokens_ptr;
    unsigned int num_tokens_for_call;

    if (nondet_choice_tokens_null) {
        tokens_ptr = NULL;
        // Se tokens_ptr é NULL, JSMN diz que retorna o número de tokens necessários.
        // O parâmetro 'num_tokens_available' ainda é usado para verificar se o *contador*
        // de tokens estimados estoura este limite.
        // "If JSMN_ERROR_NOMEM is returned, then num_tokens was not enough"
        num_tokens_for_call = num_tokens_available; // Ou um valor não determinístico menor
    } else {
        tokens_ptr = tokens;
        num_tokens_for_call = num_tokens_available;
    }

    int r = jsmn_parse(&parser, json_input_string, json_len, tokens_ptr, num_tokens_for_call);

    // 5. Asserções (Propriedades a verificar)

    // Propriedades gerais do parser após a chamada
    assert(parser.pos <= json_len); // O cursor de parsing não deve ultrapassar o comprimento da string

    if (r >= 0) { // Sucesso ou JSMN_ERROR_PART (se r=0 e json_len > 0)
        // r é o número de tokens preenchidos/necessários
        if (tokens_ptr != NULL) {
            assert(r <= (int)num_tokens_for_call); // Não deve usar mais tokens do que o disponível
        }
        // Se tokens_ptr é NULL, 'r' é o número de tokens que *seriam* necessários.
        // Nesse caso, r pode ser maior que num_tokens_for_call.

        assert(parser.toknext == r); // o próximo token a ser alocado deve ser igual a r

        // Verificar cada token retornado (se tokens_ptr não for NULL e r > 0)
        if (tokens_ptr != NULL) {
            for (int i = 0; i < r; i++) {
                // start e end devem estar dentro dos limites da string JSON
                assert(tokens_ptr[i].start >= -1); // -1 é possível para tokens não inicializados, mas JSMN deve preencher.
                                                // A documentação não especifica -1, então vamos assumir >=0.
                assert(tokens_ptr[i].start >= 0);
                assert(tokens_ptr[i].end >= tokens_ptr[i].start);
                assert(tokens_ptr[i].end <= (int)json_len); // end é exclusivo, ou inclusivo?
                                                         // "end position", "String [3..7]" => inclusivo.
                                                         // "string tokens point to the first character after the opening quote
                                                         // and the previous symbol before final quote" -> para strings.
                                                         // Para objetos/arrays, é o limite do token.

                // Tipos de token válidos
                assert(tokens_ptr[i].type == JSMN_OBJECT ||
                       tokens_ptr[i].type == JSMN_ARRAY ||
                       tokens_ptr[i].type == JSMN_STRING ||
                       tokens_ptr[i].type == JSMN_PRIMITIVE ||
                       tokens_ptr[i].type == JSMN_UNDEFINED); // UNDEFINED não deveria ser um tipo de token retornado.
                                                              // A enumeração começa com UNDEFINED = 0, então um token
                                                              // não inicializado poderia ter esse valor. Mas tokens *usados* (até r)
                                                              // deveriam ter tipos válidos.
                assert(tokens_ptr[i].type != JSMN_UNDEFINED || (tokens_ptr[i].start == -1 && tokens_ptr[i].end == -1));


                // Para objetos e arrays, size deve ser >= 0
                if (tokens_ptr[i].type == JSMN_OBJECT || tokens_ptr[i].type == JSMN_ARRAY) {
                    assert(tokens_ptr[i].size >= 0);
                    // TODO: Verificar consistência hierárquica (size vs tokens filhos)
                    // Ex: a soma dos tokens filhos + netos deve ser tokens[i].size
                    // E o próximo token após o objeto/array deve ser i + 1 + tokens[i].size (se strict order)
                    // JSMN não garante a ordem dos tokens na saída, apenas o preenchimento.
                    // O campo 'size' é o número de filhos diretos.
                } else if (tokens_ptr[i].type == JSMN_STRING || tokens_ptr[i].type == JSMN_PRIMITIVE) {
                    assert(tokens_ptr[i].size == 0); // Strings e primitivos não têm filhos
                }
            }
        }
    } else { // Erro retornado
        assert(r == JSMN_ERROR_INVAL || // JSON corrompido
               r == JSMN_ERROR_NOMEM || // Não há tokens suficientes
               r == JSMN_ERROR_PART);   // JSON incompleto

        if (r == JSMN_ERROR_NOMEM) {
            // Se tokens_ptr != NULL, isso significa que num_tokens_for_call foi insuficiente.
            // Se tokens_ptr == NULL, significa que o *número* de tokens em num_tokens_for_call
            // foi menor que o número de tokens que o parser estimou serem necessários.
            // Ou seja, parser.toknext (o contador de tokens) excedeu num_tokens_for_call.
            assert(parser.toknext > (int)num_tokens_for_call || num_tokens_for_call == 0);
        }
    }
    return 0;
}