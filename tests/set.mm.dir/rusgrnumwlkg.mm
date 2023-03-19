include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "chash.mm"
include "c1st.mm"
include "c2nd.mm"
include "cwlks.mm"
include "cexp.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "ovex.mm"
include "rabex.mm"
include "cusgr.mm"
include "cvtx.mm"
include "rusgrusgr.mm"
include "adantr.mm"
include "simpr3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "wlksnwwlknvbij.mm"
include "syl3anc.mm"
include "f1oexbi.mm"
include "sylibr.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"
include "rusgrnumwwlkg.mm"
include "eqtr3d.mm"

theorem rusgrnumwlkg
  let vw: setvar w
  let cP: class P
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume rusgrnumwwlkg.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint K w
  disjoint N w
  disjoint P w
  disjoint V w
  disjoint G n
  disjoint G v
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint P n
  disjoint P v
  disjoint V n
  disjoint V v
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint f g
  disjoint f p
  disjoint f w
  disjoint g p
  disjoint g w
  disjoint p w
  disjoint N f
  disjoint N g
  disjoint N p
  disjoint K p
  disjoint P f
  disjoint P g
  disjoint P p
  disjoint V p
  assert |- ( ( G RegUSGraph K /\ ( V e. Fin /\ P e. V /\ N e. NN0 ) ) -> ( # ` { w e. ( Walks ` G ) | ( ( # ` ( 1st ` w ) ) = N /\ ( ( 2nd ` w ) ` 0 ) = P ) } ) = ( K ^ N ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cV
    cfn
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    wa
    #
    cc0
    vp
    cv
    cfv
    cP
    wceq
    #
    vp
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    vw
    cv
    #
    c1st
    cfv
    chash
    cfv
    cN
    wceq
    cc0
    @10
    c2nd
    cfv
    cfv
    cP
    wceq
    wa
    vw
    cG
    cwlks
    cfv
    crab
    #
    chash
    cfv
    #
    cK
    cN
    cexp
    co
    @8
    cvv
    wcel
    @5
    @8
    @11
    vg
    cv
    wf1o
    vg
    wex
    #
    @9
    @12
    wceq
    @6
    vp
    @7
    cN
    cG
    cwwlksn
    ovex
    rabex
    @5
    @11
    @8
    vf
    cv
    wf1o
    vf
    wex
    #
    @13
    @5
    cG
    cusgr
    wcel
    #
    @3
    cP
    cG
    cvtx
    cfv
    #
    wcel
    #
    @14
    @0
    @15
    @4
    cG
    cK
    rusgrusgr
    adantr
    @0
    @1
    @2
    @3
    simpr3
    @4
    @17
    @0
    @2
    @1
    @17
    @3
    @2
    @17
    cV
    @16
    cP
    rusgrnumwwlkg.v
    eleq2i
    biimpi
    3ad2ant2
    adantl
    vp
    vf
    cG
    cN
    cP
    vw
    wlksnwwlknvbij
    syl3anc
    @8
    @11
    vg
    vf
    f1oexbi
    sylibr
    @8
    @11
    vg
    cvv
    hasheqf1oi
    mpsyl
    vp
    cP
    cG
    cK
    cN
    cV
    rusgrnumwwlkg.v
    rusgrnumwwlkg
    eqtr3d
end
