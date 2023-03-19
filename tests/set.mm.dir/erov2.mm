include "erov.mm"

theorem erov2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cP: class P
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
  let c.sm: class .~
  let cU: class U
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume eropr2.1: |- J = ( A /. .~ )
  assume eropr2.2: |- .+^ = { <. <. x , y >. , z >. | E. p e. A E. q e. A ( ( x = [ p ] .~ /\ y = [ q ] .~ ) /\ z = [ ( p .+ q ) ] .~ ) }
  assume eropr2.3: |- ( ph -> .~ e. X )
  assume eropr2.4: |- ( ph -> .~ Er U )
  assume eropr2.5: |- ( ph -> A C_ U )
  assume eropr2.6: |- ( ph -> .+ : ( A X. A ) --> A )
  assume eropr2.7: |- ( ( ph /\ ( ( r e. A /\ s e. A ) /\ ( t e. A /\ u e. A ) ) ) -> ( ( r .~ s /\ t .~ u ) -> ( r .+ t ) .~ ( s .+ u ) ) )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint P p
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X z
  disjoint .+ p
  disjoint .+ q
  disjoint .+ r
  disjoint .+ s
  disjoint .+ t
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ p
  disjoint .~ q
  disjoint .~ r
  disjoint .~ s
  disjoint .~ t
  disjoint .~ u
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint J p
  disjoint J q
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q p
  disjoint Q q
  disjoint Q r
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q x
  disjoint Q y
  disjoint Q z
  assert |- ( ( ph /\ P e. A /\ Q e. A ) -> ( [ P ] .~ .+^ [ Q ] .~ ) = [ ( P .+ Q ) ] .~ )

  proof
    wph
    vx
    vy
    vz
    vu
    vt
    cA
    cA
    cA
    cP
    c.pl
    c.pd
    cQ
    c.sm
    c.sm
    c.sm
    cU
    cJ
    cJ
    cU
    cU
    cX
    cX
    cX
    vs
    vr
    vq
    vp
    eropr2.1
    eropr2.1
    eropr2.3
    eropr2.4
    eropr2.4
    eropr2.4
    eropr2.5
    eropr2.5
    eropr2.5
    eropr2.6
    eropr2.7
    eropr2.2
    eropr2.3
    eropr2.3
    erov
end
