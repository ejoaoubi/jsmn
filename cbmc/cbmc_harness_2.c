#include <assert.h>
#include <stddef.h> // Para size_t
#include "jsmn.h"
// Para o CBMC, não precisamos de stdlib.h para nondet_*,
// mas pode ser útil para memset ou outros.
// O CBMC fornece as funções nondet_* intrinsecamente.
// Limites para a exploração do CBMC. Ajuste conforme necessário.
// Valores pequenos para começar.
#define MAX_JSON_INPUT_LEN 8
#define MAX_TOKENS_AVAILABLE 4


int main() {
    // 1. Declarar variáveis para jsmn_parse
    jsmn_parser parser;
    jsmntok_t tokens[MAX_TOKENS_AVAILABLE];
    char json_input[MAX_JSON_INPUT_LEN];
    size_t json_len;
    unsigned int num_tokens_param; // Número de tokens passados para jsmn_parse

    // 2. Inicializar entradas com valores não-determinísticos
    // Comprimento da string JSON
    json_len = nondet_size_t();
    __CPROVER_assume(json_len < MAX_JSON_INPUT_LEN); // json_len pode ser de 0 a MAX_JSON_INPUT_LEN-1

    // Conteúdo da string JSON
    for (size_t i = 0; i < json_len; i++) {
        json_input[i] = nondet_char();
        // Opcional: Restringir caracteres para serem ASCII imprimíveis se quiser testar JSON mais "típico"
        // __CPROVER_assume(json_input[i] >= 32 && json_input[i] < 127);
    }
    json_input[json_len] = '\0'; // JSMN usa '\0' como terminador em alguns loops

    // Número de tokens disponíveis para o parser
    num_tokens_param = nondet_uint();
    // JSMN pode ser chamado com 0 tokens para apenas contar,
    // mas para verificar a escrita de tokens, precisamos de pelo menos 1.
    // Para simplificar, vamos assumir que queremos testar a escrita.
    __CPROVER_assume(num_tokens_param > 0 && num_tokens_param <= MAX_TOKENS_AVAILABLE);

    // Inicializar o parser JSMN
    jsmn_init(&parser);

    // Opcional: inicializar o array de tokens para um estado conhecido (debug)
    // Se não o fizermos, o CBMC tratará o conteúdo inicial como não-determinístico.
    // for (unsigned int i = 0; i < num_tokens_param; i++) {
    //     tokens[i].type = JSMN_UNDEFINED;
    //     tokens[i].start = -1;
    //     tokens[i].end = -1;
    //     tokens[i].size = 0;
    //     #ifdef JSMN_PARENT_LINKS
    //     tokens[i].parent = -1;
    //     #endif
    // }


    // 3. Chamar a função a ser verificada
    int result = jsmn_parse(&parser, json_input, json_len, tokens, num_tokens_param);

    // 4. Adicionar asserções (propriedades a verificar)

    // Propriedade 1: O parser não deve avançar para além do final da string de entrada.
    __CPROVER_assert(parser.pos <= json_len, "Parser position (pos) exceeds json_len");

    // Propriedade 2: O número de tokens a alocar (toknext) não deve exceder o número de tokens fornecidos.
    __CPROVER_assert(parser.toknext <= num_tokens_param, "parser.toknext exceeds num_tokens_param");

    if (result >= 0) { // Se o parse foi bem-sucedido (ou parcialmente) e retornou uma contagem de tokens
        // Propriedade 3: O número de tokens retornados não deve exceder num_tokens_param.
        // (result é a contagem de tokens *potenciais* se tokens fosse NULL,
        //  ou o número de tokens de alto nível preenchidos)
        // Esta asserção pode ser muito forte dependendo da interpretação de 'result'.
        // O JSMN pode retornar um 'result' maior que 'num_tokens_param' se não houver tokens suficientes (JSMN_ERROR_NOMEM é -1).
        // No entanto, se result > 0, indica o número de tokens encontrados.
        // O 'count' interno que 'result' representa pode exceder 'num_tokens_param' antes de retornar JSMN_ERROR_NOMEM.
        // A documentação diz: "returns the number of tokens parsed".
        // Se tokens != NULL, o número de tokens preenchidos é parser.toknext.
        // O 'result' é o número total de tokens que *seriam* necessários.
        // Se JSMN_ERROR_NOMEM for retornado, 'result' é -1.
        // Se não houver erro, 'result' é o número de tokens que *seriam* necessários.
        // Vamos focar-nos nos tokens realmente escritos: parser.toknext
        // __CPROVER_assert(result <= (int)num_tokens_param, "Resulting token count exceeds num_tokens_param");

        // Propriedade 4: Verificar os tokens preenchidos (até parser.toknext)
        for (unsigned int i = 0; i < parser.toknext; i++) {
            if (tokens[i].start != -1) { // Se o token foi inicializado
                __CPROVER_assert(tokens[i].start >= 0, "Token start is negative");
                __CPROVER_assert((size_t)tokens[i].start < json_len, "Token start is out of bounds (>= json_len)");

                if (tokens[i].end != -1) { // O 'end' pode ser -1 se um objeto/array não for fechado
                    __CPROVER_assert(tokens[i].end >= 0, "Token end is negative");
                    // 'end' é exclusivo, então pode ser igual a json_len
                    __CPROVER_assert((size_t)tokens[i].end <= json_len, "Token end is out of bounds (> json_len)");
                    __CPROVER_assert(tokens[i].start <= tokens[i].end, "Token start is after end");
                }
            }
            // Tipos de tokens devem ser válidos
            __CPROVER_assert(
                tokens[i].type == JSMN_UNDEFINED || // Pode ser UNDEFINED se alocado mas não preenchido completamente
                tokens[i].type == JSMN_OBJECT ||
                tokens[i].type == JSMN_ARRAY ||
                tokens[i].type == JSMN_STRING ||
                tokens[i].type == JSMN_PRIMITIVE,
                "Invalid token type"
            );

            __CPROVER_assert(tokens[i].size >= 0, "Token size is negative");

            #ifdef JSMN_PARENT_LINKS
            if (tokens[i].parent != -1) {
                __CPROVER_assert(tokens[i].parent < (int)parser.toknext, "Token parent index out of bounds");
                // E o pai deve ser um token anterior ou um token "superior" na hierarquia
                // Esta asserção pode ser mais complexa de validar corretamente.
                // __CPROVER_assert(tokens[i].parent < (int)i, "Token parent index not preceding current token");
            }
            #endif
        }
    } else { // Se ocorreu um erro (result < 0)
        __CPROVER_assert(result == JSMN_ERROR_NOMEM ||
                         result == JSMN_ERROR_INVAL ||
                         result == JSMN_ERROR_PART,
                         "Invalid error code returned");
    }

    // CBMC verifica automaticamente acesso fora dos limites, ponteiros nulos, etc.

    return 0;
}