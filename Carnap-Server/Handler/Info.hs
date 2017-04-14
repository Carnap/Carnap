module Handler.Info where

import Import
import Text.Shakespeare.Text
--import Text.Hamlet

getInfoR :: Handler Html
getInfoR = do
    defaultLayout $ do
        addScript $ StaticR ghcjs_rts_js
        addScript $ StaticR ghcjs_allactions_lib_js
        addScript $ StaticR ghcjs_allactions_out_js
        setTitle "Carnap - About"
        $(widgetFile "infopage")
        addStylesheet $ StaticR css_tree_css
        addStylesheet $ StaticR css_exercises_css
        -- TODO : split out the stuff specifically relating to exercises
        addScript $ StaticR ghcjs_allactions_runmain_js

-- TODO remove submit option on these.
proofcheck :: Int -> Text -> Text -> Text -> HtmlUrl url
proofcheck n cls goal proof = 
        [hamlet|
        <div class="exercise">
            <span>example #{show n}
            <div class="#{cls}">
                <div.goal>#{goal}
                <textarea>#{proof}
                <div.output>
        |]

-- XXX function that strips text of indentation and line-numbers.
aristotleTheorem = [st|
Show: P\/-P
    Show: --(P\/-P)
        -(P\/-P):AS
        Show: -P
            P:AS
            P\/-P:ADD 5
        :ID 6 3
        P\/-P:ADD 4
    :ID 3 8
    P\/-P:DNE 2
:DD 10
|]

pierceTheorem = [st|
  (P->Q)->P:AS
     -P:AS
        P:AS
          Q:AS
          P:R 3
          -P:R 2
        Q:-E 4-6
     P->Q:CI 3-7
     P:CE 8 1
     -P:R 2
  P:-E 2-10
((P->Q)->P)->P:CI 1-11
|]

comprehensionTheorem = [st|
Show EXAx(F(x)/\G(x)<->X(x))
   Show Ax(F(x)/\G(x)<->\y[F(y)/\G(y)](x))
       Show F(c)/\G(c)->\y[F(y)/\G(y)](c)
            F(c)/\G(c):AS
            \y[F(y)/\G(y)](c):ABS 4
       :CD 5
       Show \y[F(y)/\G(y)](c)->F(c)/\G(c)
            \y[F(y)/\G(y)](c):AS
            F(c)/\G(c):APP 8
       :CD 9
       F(c)/\G(c)<->\y[F(y)/\G(y)](c):CB 3 7
   :UD 11
   EXAx(F(x)/\G(x)<->X(x)):EG 2
:DD 13
|]

russellTheorem = [st|
Show -ExAy(-F(y,y) <-> F(x,y))
    ExAy(-F(y,y)<->F(x,y)):AS
    Show: -ExAy(-F(y,y) <-> F(x,y))
        Ay(-F(y,y)<->F(c_1,y)):AS
        -F(c_1,c_1)<->F(c_1,c_1):UI 4
        Show:-F(c_1,c_1)
            F(c_1,c_1):AS
            F(c_1,c_1)->-F(c_1,c_1) :BC 5
            -F(c_1,c_1) :MP 8 7
        :ID 7 9
        -F(c_1,c_1) -> F(c_1,c_1) :BC 5
        F(c_1,c_1) :MP 11 6
        Show: -ExAy(-F(y,y) <-> F(x,y))
        :ID 6 12
    :ED 13 2 4
:ID 2 3
|]

russellTheoremForallx = [st|
    ExAy(-Fyy <-> Fxy):AS
       Ay(-Fyy<->Fry):AS
       -Frr<->Frr:AE 2
            -Frr:AS
            Frr:<->E 3 4
            -Frr:R 4
       Frr:-E 4-6
       -Frr:<->E 7 3
            ExAy(-Fyy <-> Fxy):AS
            Frr:R 7
            -Frr:R 8
       -ExAy(-Fyy <-> Fxy):-I 9-11
    -ExAy(-Fyy <-> Fxy):EE 1 2-12
    ExAy(-Fyy <-> Fxy):R 1
-ExAy(-Fyy <-> Fxy):-I 1-14
|]

