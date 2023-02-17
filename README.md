# Projeto

1 - Verificação da Segurança de Sistemas Dinâmicos
José Manuel Valença (jmvalenca@gmail.com)

Este trabalho vem na continuação da disciplina de Lógica Computacional nomeadamente no uso de sistemas STAT para verificação da segurança em sistemas dinâmicos. O trabalho envolve os seguintes conceitos:
- sistemas dinâmicos sob a forma de CFA's ("control flow autómato")
- descrição intermédia sob a forma de SFOTS ("sistemas de transição") ou transformadores de predicados (WP ou SP),
- metodologias de verificação: k-indução, "interpolant based" e "property directed reachability" (só em FSM's)
Pretende-se construir um programa Python que
- aceite uma descrição de um CFA sob a forma de um grafo com atributos que sejam expressões pySMT
- aceite as instruções do operador sob a forma de uma "tática" que descreva as metodologias usadas
