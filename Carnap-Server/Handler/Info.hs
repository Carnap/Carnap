module Handler.Info where

import Import
import Text.Shakespeare.Text
--import Text.Hamlet

getInfoR :: Handler Html
getInfoR = do
    defaultLayout $ do
        addScript $ StaticR js_popper_min_js
        addScript $ StaticR ghcjs_rts_js
        addScript $ StaticR ghcjs_allactions_lib_js
        addScript $ StaticR ghcjs_allactions_out_js
        addScript $ StaticR klement_proofs_js
        addScript $ StaticR klement_syntax_js
        setTitle "Carnap - About"
        $(widgetFile "infopage")
        addStylesheet $ StaticR css_tree_css
        addStylesheet $ StaticR css_exercises_css
        addStylesheet $ StaticR klement_proofs_css
        -- TODO : split out the stuff specifically relating to exercises
        addScript $ StaticR ghcjs_allactions_runmain_js

-- TODO remove submit option on these.
proofcheck :: Int -> Text -> Text -> Text -> Text -> HtmlUrl url
proofcheck n sys opts goal proof = 
        [hamlet|
        <div class="exercise">
            <span>example #{show n}
            <div data-carnap-type="proofchecker" data-carnap-options="#{opts}" data-carnap-system="#{sys}" data-carnap-goal="#{goal}">
                #{strip proof}
        |]
    where strip = dropWhile (== '\n')

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

russellTheoremCalgary = [st|
    ExAy(-Fyy <-> Fxy):AS
        Ay(-Fyy<->Fry):AS
        -Frr<->Frr:AE 2
             -Frr:AS
             Frr:<->E 3 4
             !?:!?I 4 5
        --
             Frr:AS
             -Frr:<->E 3 8
             !?:!?I 8 9
        !?:TND 4-6 8-10
    !?:EE 1 2-11
-ExAy(-Fyy <-> Fxy):-I 1-12
|]

inverseTheorem = [st|
Show: AX2EY2∀x∀y(X2(x,y) ↔ Y2(y,x))
  Show: ∀x∀y(X2(x,y) ↔ \w\v[X2(v,w)](y,x))
    Show: ∀y(X2(a,y) ↔ \w\v[X2(v,w)](y,a))
      Show: X2(a,b) -> \w\v[X2(v,w)](b,a)
        X2(a,b):AS
        \w\v[X2(v,w)](b,a):ABS2 5
      :CD 6
      Show: \w\v[X2(v,w)](b,a)-> X2(a,b)
        \w\v[X2(v,w)](b,a):AS
        X2(a,b):APP2 9
      :CD 10
      X2(a,b) <-> \x_1\x_2[X2(x_2,x_1)](b,a):CB 4 8
    :UD 12
  :UD 3
  EY2∀x∀y(X2(x,y) ↔ Y2(y,x)):EG2 2
:UD2 15
|]

adjunctionTheorem = [st|
Show P->(Q->R):CD
    P:AS
    Show Q->R:CD
      Q:AS
      P/\Q->R:PR
      P/\Q:&I 2 4
      R:->O 5 6
|]

axiomFiveTheorem = [st|
Show <>[]P->[]P  /0   :CD
  <>[]P          /0   :AS
  Show []P       /0   :ND
    Show P       /0-1 :DD
      []P        /0-2 :<>O 2
      P          /0-1 :[]O(5) 5
|]

axiomBTheorem = [st|
Show <>[]P->P /0   :CD
  <>[]P       /0   :AS
  []P         /0-1 :<>O 2
  P           /0   :[]O(b) 3
|]

barcanTheorem = [st|
Show Ax[]Fx->[]AxFx  /0   :CD
  Ax[]Fx             /0   :AS
  Show []AxFx        /0   :ND
    Show AxFx        /0-1 :UD
      Show Fa        /0-1 :DD
        []Fa         /0   :AO 2
        Fa           /0-1 :[]O 6
|]

bisectorTheorem = [st|
AxAyAz(F(x,g(y,z))↔h(x,y) = h(x,z)) :PR
Show AwAxAyAz(F(w,g(x,y))∧F(w,g(x,z))→F(w,g(y,z)))
 Show AxAyAz(F(a,g(x,y))∧F(a,g(x,z))→F(a,g(y,z)))
  Show AyAz(F(a,g(b,y))∧F(a,g(b,z))→F(a,g(y,z)))
   Show Az(F(a,g(b,c))∧F(a,g(b,z))→F(a,g(c,z)))
    Show F(a,g(b,c))∧F(a,g(b,d))→F(a,g(c,d))
     F(a,g(b,c))∧F(a,g(b,d))             :AS
     F(a,g(b,c))                         :S 7
     F(a,g(b,d))                         :S 7
     AyAz(F(a,g(y,z))<> h(a,y) = h(a,z)) :UI 1
     Az(F(a,g(b,z))<> h(a,b) = h(a,z))   :UI 10
     F(a,g(b,c)) ↔ h(a,b) = h(a,c)       :UI 11
     F(a,g(b,d)) ↔ h(a,b) = h(a,d)       :UI 11
     F(a,g(b,c)) → h(a,b) = h(a,c)       :BC 12
     F(a,g(b,d)) → h(a,b) = h(a,d)       :BC 13
     h(a,b) = h(a,c)                     :MP 8 14
     h(a,b) = h(a,d)                     :MP 9 15
     h(a,c) = h(a,d)                     :LL 16 17
     Az(F(a,g(c,z)) ↔ h(a,c) = h(a,z))   :UI 10
     F(a,g(c,d)) ↔ h(a,c) = h(a,d)       :UI 19
     h(a,c) = h(a,d) → F(a,g(c,d))       :BC 20
     F(a,g(c,d))                         :MP 18 21
    :CD 22
   :UD 6
  :UD 5
 :UD 4
:UD 3
|]
