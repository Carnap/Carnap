# templates/homepage.hamlet
HomepageWelcome: Bem-vindo ao Carnap
HomepageSubtitle: Uma plataforma para Lógica Formal em Haskell
HomepageHeader: Do que se trata?
HomepageTextPrefix1: Carnap é uma plataforma livre e aberta escrita em
HomepageTextLink1: Haskell
HomepageTextSuffix1: para ensinar e estudar lógica formal.
HomepageTextPrefix2: Carnap sustenta e enriquece cursos de lógica
HomepageTextLink2: em dezenas de faculdades e universidades
HomepageTextSuffix2: ao redor do mundo.
HomepageText3: Se você é estudante em um curso que usa Carnap, por favor siga os links no topo da página para entrar na plataforma e acessar os materiais de curso.
HomepageTextPrefix4: Se está apenas curioso sobre o Carnap, você pode encontrar informações gerais em nossa
HomepageTextLink4: página
HomepageTextSuffix4: de informações.
HomepageTextPrefix5: Se você está interessado no projeto e gostaria de usar Carnap nos cursos ministra, ou gostaria de se envolver de alguma outra maneira, por favor sinta-se livre para
HomepageTextLink5: entrar em contato!


# templates/infopage.hamlet
InfopageAboutCarnap: Sobre o Carnap
InfopageWhatIs: O que é o Carnap?
InfopageWhatFor: Para que serve o Carnap?
InfopageHowToUse: Como posso usar o Carnap?
InfopageWhyName: Por que "Carnap"?
InfopageWhoUses: Quem usa o Carnap?
InfopageHowWorks: Como o Carnap funciona?
InfopageHowHelp: Como posso me envolver?
InfopageCarnapQuote1: "A aceitação ou rejeição das formas linguísticas abstratas, assim como a aceitação ou rejeição de quaisquer outras formas linguísticas em qualquer outro campo da ciência, será finalmente decidida por sua eficiência enquanto instrumento, a razão entre os resultados alcançados e a quantidade e complexidade dos esforços requeridos. Decretar proibições dogmáticas de certas formas linguísticas em vez de avaliá-las pelo seu sucesso ou fracasso no uso prático, é pior do que fútil: é positivamente alarmante porque pode obstruir o progresso científico."
InfopageCarnapQuote2: Atribuamos àqueles que trabalham em algum campo especial da investigação a liberdade para usar qualquer forma de expressão que lhes pareça útil; o trabalho nesse campo conduzirá mais cedo ou mais tarde à eliminação daquelas formas que não possuem nenhuma função útil. Sejamos prudentes ao fazer asserções e tenhamos uma atitude crítica ao examiná-las, mas sejamos tolerantes ao permitir as formas linguísticas."
InfopageCarnapQuoteSource: Empirismo, Semântica e Ontologia
InfopageWhatIsText: Carnap é uma plataforma em Haskell gratuita e de código aberto para criar e explorar linguagens formais, lógicas e semânticas. Ela permite de modo simples e rápido que você defina linguagens formais, construa lógicas para tais linguagens e estipule sua semântica. Carnap então usa as suas especificações para descobrir como verificar provas em uma variedade de sistemas formais usando a sua lógica, como encontrar os significados para expressões compostas e muito mais. 
InfopageDemos: Demonstração
InfopageDemosHere: Aqui seguem alguns exemplos rápidos ilustrando o que Carnap pode fazer.
InfopageDemosText1: Este é um quadro de prova com o sistema para a Lógica Proposicional de Kalish e Montague. Você pode manipular diretamente a prova ao digitar no quadro de prova e ver os efeitos de suas mudanças ao passar o mouse sobre as marcações em cada linha à direita.
InfopageDemosText2: Este é um quadro renderizado de prova com o sistema para a Lógica Proposicional de Kalish e Montague. Esse tipo de quadro de prova mostra visualmente a estrutura da demonstração sendo desenvolvida.
InfopageDemosText3: Este é um quadro renderizado de prova com a variação de Hardegree de um sistema de Montague. 
InfopageDemosTextPrefix4: Este é um quadro de prova com um sistema Fitch, que usa regras do 
InfopageDemosTextItalics4: Logic Book
InfopageDemosTextSuffix4: e renderiza a estrutura da prova no estilo Fitch.
InfopageDemosText5: Este é um quadro de prova com o sistema de Kalish e Montague para a Lógica de Primeira-Ordem, mostrando a prova do Teorema de Russell.
InfopageDemosTextPrefix6: Esta é uma prova com o sistema de dedução natural estilo Lemmon de Goldfarb, do manual
InfopageDemosTextItalics6: Deductive Logic
InfopageDemosTextSuffix6:
InfopageDemosText7: Segue uma prova do fato que as bissetrizes dos lados de um triângulo sempre se encontram em um ponto (a partir da assunção de que um ponto está na bissetriz de um segmento se e somente se é equidistante aos pontos finais daquele segmento.) "F(x,y)" abrevia que "x está sobre y", "g(y,z)" abrevia "o bissector do segmento dado por y e z", e "h(x,z)" abrevia "a distância  de x a z".
InfopageDemosText8: (Devido ao número de variáveis, isto pode tomar um tempo para carregar inicialmente. Uma vez carregado, deveria responder rapidamente a mudanças.)
InfopageDemosTextPrefix9: Seguem mais duas provas do teorema de Russell, esta vez utilizando uma versão do sistema QL, do manual livre e aberto do P.D. Magnus.
InfopageDemosTextLinkA9:  Forall x
InfopageDemosTextInfixA9: , e o sistema LPO do
InfopageDemosTextLinkB9: Remix de Calgary
InfopageDemosTextSuffix9: do Forall x.
InfopageDemosText10: Note que mudamos como as fórmulas são tratadas (dispensando os parêntesis para os argumentos de predicados), de modo a se adequar ao estilo do Forall x.
InfopageDemosText11: Isto é um quadro de prova com o sistema de Kalish e Montague para a Lógica de Segunda Ordem Monádica, mostrando como provar uma instância do esquema da compreensão, usando a regra de abstração de predicados.
InfopageDemosText12: Isto é um quadro de prova que toda relação tem um inverso, em um sistema poliádico de Segunda Ordem.
InfopageDemosTextPrefix13: Esta é uma prova que o conjunto potência de um conjunto transitivo é transitivo (exercício 3, capítulo 3.3 do livro
InfopageDemosTextItalics13: Deductive Logic
InfopageDemosTextSuffix13: , de Velleman), em um sistema elementar de teoria dos conjuntos.
InfopageDemosTextPrefix14: Seguem provas dos axiomas 5 e B nos sistemas de dedução natural para lógicas modais K5 e KTB, no estilo do livro de Hardegree, chamado
InfopageDemosTextLink14: "Modal Logic"
InfopageDemosTextSuffix14:
InfopageDemosTextPrefix15: Estes usam 
InfopageDemosTextLink15: Fira Logic
InfopageDemosTextSuffix15: para símbolos lógicos mais bonitos e usa linhas verticais para ajudar a indicar visualmente o escopo de cada subprova.
InfopageDemosTextPrefix16: Aqui está uma prova da Fórmula Barcan em um sistema modal com quantificação ingênua, baseado no sistema MPL do livro
InfopageDemosTextLink16: "Modal Logic"
InfopageDemosTextSuffix16: de Hardegree.
InfopageDemosTextPrefix17: O Carnap suporta provas escritas no cálculo de sequentes, via
InfopageDemosTextLink17: ProofJS
InfopageDemosTextSuffix17:
InfopageDemosText18: Entre os sistemas suportados estão as variantes proposicional e de primeira ordem dos sistemas LK e LJ originais de Gentzen.
InfopageDemosTextPrefix19: O Carnap também inclui uma API JSON, que torna possível a criação de GUIs em JavaScript puro que usam o Carnap no segundo-plano para verificação de provas no navegador. Aqui vai um exemplo de tal GUI, adaptado do
InfopageDemosTextLink19: verificador de prova de Keven Klement para o "Forall x"
InfopageDemosTextSuffix19: que utiliza o sistema SL do "Forall x" de P.D. Magnus.
InfopageDemosText20: exemplo 17

InfopageWhy1: Para que serve o Carnap?
InfopageWhy2: A intenção do Carnap é para uso de educadores, estudantes e pesquisadores que trabalham com lógica. O Carnap possibilita que educadores criem exercícios interativos e materiais didáticos, também permite que estudantes obtenham comentários rápidos e úteis enquanto aprendem métodos semânticos e sintáticos para determinar o que segue de que. O Carnap também pode ser utilizado para investigações em lógica assistidas por computador, permitindo que pesquisadores interessados em sistemas formais não-ortodoxos possam implementar rapidamente protótipos, tanto de verificadores de prova, quanto de ferramentas semânticas.

InfopageUsage1: Como utilizar o Carnap agora mesmo?
InfopageUsage2: Você pode utilizar o Carnap para ministrar suas aulas de lógica!
InfopageUsagePrefix3: Tudo o que você precisa fazer é
InfopageUsageLinkA3: criar uma conta
InfopageUsageInfix3: e então 
InfopageUsageLinkB3: entrar em contato
InfopageUsageSuffix3: para se registrar como um instrutor.
InfopageUsage4: Uma vez cadastrado como instrutor, você pode utilizar este site --o que você está acessando agora, carnap.pontofixo.net.br-- para ministrar suas aulas e ter tarefas extraclasse automaticamente corrigidas.
InfopageUsagePrefix5: Você pode, ou atribuir questões a partir do livro texto livre e aberto
InfopageUsageLink5: manual
InfopageUsageSuffix5: hospedado aqui (o livro está em inglês), ou usar seu próprio manual e criar para o seu sistema preferido, questionários a serem corrigidos automaticamente.
InfopageUsagePrefix6: O Carnap atualmente suporta tabelas de verdade, traduções, exercícios de sintaxe, bem como deduções compatíveis com os sistemas formais usados pelo livro de Kalish e Montague, chamamdo
InfopageUsageItalicsA6: Logic
InfopageUsageInfixA6: o livro de Bergmann e More, chamado
InfopageUsageItalicsB6: Logic Book
InfopageUsageInfixB6: o livro de Hardegree, chamado
InfopageUsageItalicsC6: Modal Logic
InfopageUsageInfixC6: o livro de P.D. Magnus, chamado
InfopageUsageItalicsD6: Forall x
InfopageUsageInfixD6: e para o Remix de Calgary de
InfopageUsageItalicsE6: Forall x
InfopageUsageSuffix6:
InfopageUsage7: Mas a ambição deste projeto é a cobertura máxima. Assim, se o seu sistema favorito não é suportado, entre em contato para vermos a possibilidade de adicioná-lo.
InfopageUsagePrefix8: A documentação para potenciais instrutores pode ser encontrada
InfopageUsageLink8: aqui
InfopageUsageSuffix8:


InfopageName1: Por que "Carnap"?
InfopageName2: Carnap foi nomeado em referência a Rudolf Carnap, o filósofo citado acima.
InfopageName3: Carnap (o filósofo) notoriamente advogou uma abordagem tolerante e experimental da lógica. Carnap (o programa) é pluralista por natureza. Regras de inferência são especificadas declarativamente, tornando fácil a adição de novas lógicas além daquelas já fornecidas para uma dada linguagem. Os algoritmos para verificar se as inferências são corretas são aplicáveis a uma variedade ampla de linguagens, tornando fácil a introdução de novas linguagens.
InfopageName4: Carnap (o filósofo) também tinha muito a dizer sobre tipos lógicos, e como sua ignorância pode deixar você com crenças que não funcionam muito bem. Carnap (o programa) é escrito em Haskell, uma linguagem de programação estaticamente tipada e puramente funcional, que usa a teoria dos tipos lógicos para assegurar a correção do código.

InfopageWho1: Quem usa o Carnap?
InfopageWho2: O Carnap foi inicialmente desenvolvido na Kansas State University, mas agora é utilizado em dezenas de centros de ensino ao redor do mundo. Aqui segue uma lista (incompleta):

InfopageHow1: Como o Carnap funciona?
InfopageHow2: Bem, isto é um pouco técnico. Seguem alguns dos truques envolvidos.
InfopageHowPrefix3: Essencialmente, o sistema de tipos de Haskell possibilita representar diferentes categorias léxicas como tipos de dados, e permite combinar esses tipos de dados léxicos em um tipo de dado mais amplo, representando um léxico (utilizando algo como o método descrito em
InfopageHowLink3: este artigo
InfopageHowSuffix3: ), e definir uma linguagem como o resultado de aplicar gramaticalmente distintos elementos do léxico um ao outro.
InfopageHow4: O resumo é que, usando Carnap, você pode definir uma linguagem como o resultado de juntar categorias léxicas predefinidas. Graças às typeclasses do Haskell, suas linguagens herdarão várias propriedades úteis que suas categorias léxicas constituintes possuem (por exemplo, linguagens que contem a categoria léxica de conectivos booleanos automaticamente saberão como tratar e mostrar o símbolo para "e", ou como computar o valor semântico para a conjunção a partir dos valores semânticos dos seus constituintes). E, por causa da tipagem estática do Haskell, e o truque de representar categorias léxicas como tipos, há a garantia que qualquer erro de programação, potencialmente resultando em uma expressão não gramatical, será detectado quando você tentar compilar o programa.
InfopageHow5: Ao representar uniformemente uma ampla classe de linguagens (como resultado de juntar as categorias léxicas), nós também acabamos sendo capazes de manipulá-los uniformemente. Em particular, nós podemos utilizar algoritmos completamente genéricos para coisas como substituição de variáveis, valoração semântica,  β-normalização, unificação de ordem superior … tudo de bom que você precisa para, por exemplo, verificar a correção de provas, usando apenas a especificação de quais inferências são aceitáveis. Assim, nós apenas precisamos escrever o códico para estes algoritmos uma vez; então utilizaremos este código para qualquer linguagem definida na plataforma Carnap.
InfopageHowPrefix6: Então essa é a ideia. Se você gostaria de aprender mais sobre os detalhes, você pode inspecionar o código, falar com um desenvolvedor, ou dar uma olhada  
InfopageHowLink6: neste artigo 
InfopageHowSuffix6:

InfopageContributing1: Como me envolver?
InfopageContributingPrefix2: Se você gostaria de apoiar o Carnap, por favor considere dar-nos uma estrela no
InfopageContributingLink2: Github
InfopageContributingSuffix2:
InfopageContributing3: Se você tiver sugestões, pedidos de funcionalidades, ou quiser reportar um erro, você pode também nos encontrar no
InfopageContributingPrefix4: Para questões gerais ou discussões, você também pode nos encontrar no
InfopageContributingLinkA4: Matrix
InfopageContributingInfixA4: para o qual existe uma ponte no IRC em
InfopageContributingLinkB4: ircs://irc.libera.chat:6697/carnap
InfopageContributingInfixB4: ou por
InfopageContributingLinkC4: email
InfopageContributingSuffix4:
InfopageContributing5: Se você gostaria de contribuir com o código do projeto --qualquer coisa desde um novo algoritmo de unificação a um ajuste ao CSS ou a um modelo pandoc-- faça uma solicitação de modificação (pull request)

# templates/auth-layout.hamlet, templates/default-layout.hamlet
LayoutAbout: Sobre
LayoutBook: Livro
LayoutMessage: Mensagem
LayoutUserHome: Página do usuário
LayoutInstructorHome: Página do instrutor
LayoutSharedDocuments: Documentos compartilhados
LayoutSharedDocumentation: Documentação
LayoutLogout: Sair
LayoutLogin: Entrar

# templates/documentIndex.hamlet

DocumentIndexFilterByTag: Filtrar por Tag
DocumentIndexPubliclyShared: Compartilhado Publicamente
DocumentIndexInstructorsOnly: Para instrutores

# templates/passwordEntry.hamlet

PasswordEntryRequest: Por favor entre a chave de acesso para esta tarefa

# templates/register.hamlet

RegisterNeedTo: Parece que você necessita se registrar
RegisterPleaseEnter: Por favor insira as seguintes informações:

# templates/review.hamlet

ReviewNothingToReview: Nada para corrigir
ReviewAllProblems: Todos problemas
ReviewNeedingReview: Necessita correção

# templates/carnap-book.hamlet

CarnapBookTableOfContents: Table of Contents:
CarnapBookChapters: Chapters:
CarnapBookChapter: Chapter
CarnapBookAppendix: Appendix
CarnapBookSpecialSections: Special Sections:
CarnapBookIndexOfRules: Index of Rules
CarnapBookLicense: is licensed under a

# templates/user.hamlet

UserPageHeader1: Página inicial de
UserPageText1: Esta é sua página inicial, onde você pode acompanhar seu progresso no curso, e encontrar outras informações úteis.
UserPageTextInstructor: Sua página de instrutor está
UserPageTextInstructorLink: aqui
UserPageTable1Title: Exercícios a entregar
UserPageTable1DueDates: Datas de entrega
UserPageTable2Title: Total de pontos obtidos
UserPageTable3Title: Exercícios entregues
UserPageTable3Source: Exercício
UserPageTable3Exercise: Item
UserPageTable3Content: Conteúdo
UserPageTable3Submitted: Enviado
UserPageTable3Points: Pontos
UserPageTable3Type: Tipo
UserPageTable4Title: Seu Perfil
PersonalInformation: Informação Pessoal

#Handler/User.hs

UserNotEnrolled: Você não está atualmente inscrito em nenhuma disciplina. Você pode se inscrever em uma disciplina editando sua informação pessoal, abaixo.
NoExistingAssignment: Exercício inexistente

Assignment: Exercício
DueDate: Data de Entrega
Description: Descrição
ProblemSet: Exercício
NoDueDate: Sem data de entrega

UserFirstName: Primeiro Nome
UserLastName: Último Nome
UserCourseEnrollment: Disciplina
UserUniversityId: Número de Matrícula

Unenroll: Desinscrever-se
Edit: Editar

NoUserPage: Este usuário não existe
