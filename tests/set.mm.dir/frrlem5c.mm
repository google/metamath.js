include "wss.mm"
include "cuni.mm"
include "wfun.mm"
include "uniss.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ssid.mm"
include "frrlem5b.mm"
include "ax-mp.mm"
include "wcel.mm"
include "wex.mm"
include "cop.mm"
include "eluni.mm"
include "df-br.mm"
include "anbi1i.mm"
include "exbii.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "frrlem5.mm"
include "impcom.mm"
include "an4s.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dffun2.mm"
include "mpbir2an.mm"
include "funss.mm"
include "mpisyl.mm"

theorem frrlem5c
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let va: setvar a
  assume frrlem5.1: |- R Fr A
  assume frrlem5.2: |- R Se A
  assume frrlem5.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint A g
  disjoint f g
  disjoint A h
  disjoint h x
  disjoint h y
  disjoint f h
  disjoint G h
  disjoint G g
  disjoint g u
  disjoint u v
  disjoint u x
  disjoint g v
  disjoint g x
  disjoint v x
  disjoint g y
  disjoint h u
  disjoint h v
  disjoint R g
  disjoint R h
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint f z
  disjoint G z
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint C g
  disjoint B g
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint g h
  disjoint A a
  disjoint a f
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint a g
  disjoint B a
  disjoint G a
  disjoint R a
  assert |- ( C C_ B -> Fun U. C )

  proof
    cC
    cB
    wss
    cC
    cuni
    #
    cB
    cuni
    #
    wss
    @1
    wfun
    #
    @0
    wfun
    cC
    cB
    uniss
    @2
    @1
    wrel
    #
    vx
    cv
    #
    vu
    cv
    #
    @1
    wbr
    #
    @4
    vv
    cv
    #
    @1
    wbr
    #
    wa
    #
    vu
    vv
    weq
    #
    wi
    #
    vv
    wal
    #
    vu
    wal
    vx
    wal
    cB
    cB
    wss
    @3
    cB
    ssid
    vx
    vy
    cA
    cB
    cB
    cR
    vf
    cG
    frrlem5.1
    frrlem5.2
    frrlem5.3
    frrlem5b
    ax-mp
    @12
    vx
    vu
    @11
    vv
    @9
    @4
    @5
    vg
    cv
    #
    wbr
    #
    @13
    cB
    wcel
    #
    wa
    #
    @4
    @7
    vh
    cv
    #
    wbr
    #
    @17
    cB
    wcel
    #
    wa
    #
    wa
    #
    vh
    wex
    vg
    wex
    #
    @10
    @9
    @16
    vg
    wex
    #
    @20
    vh
    wex
    #
    wa
    @22
    @6
    @23
    @8
    @24
    @4
    @5
    cop
    #
    @1
    wcel
    @25
    @13
    wcel
    #
    @15
    wa
    #
    vg
    wex
    @6
    @23
    vg
    @25
    cB
    eluni
    @4
    @5
    @1
    df-br
    @16
    @27
    vg
    @14
    @26
    @15
    @4
    @5
    @13
    df-br
    anbi1i
    exbii
    3bitr4i
    @4
    @7
    cop
    #
    @1
    wcel
    @28
    @17
    wcel
    #
    @19
    wa
    #
    vh
    wex
    @8
    @24
    vh
    @28
    cB
    eluni
    @4
    @7
    @1
    df-br
    @20
    @30
    vh
    @18
    @29
    @19
    @4
    @7
    @17
    df-br
    anbi1i
    exbii
    3bitr4i
    anbi12i
    @16
    @20
    vg
    vh
    eeanv
    bitr4i
    @21
    @10
    vg
    vh
    @14
    @18
    @15
    @19
    @10
    @15
    @19
    wa
    @14
    @18
    wa
    @10
    vx
    vy
    vv
    vu
    cA
    cB
    cR
    vf
    vg
    vh
    cG
    frrlem5.1
    frrlem5.2
    frrlem5.3
    frrlem5
    impcom
    an4s
    exlimivv
    sylbi
    ax-gen
    gen2
    vx
    vu
    vv
    @1
    dffun2
    mpbir2an
    @0
    @1
    funss
    mpisyl
end
