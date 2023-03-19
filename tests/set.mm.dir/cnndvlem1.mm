include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cdv.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "wtru.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "c3.mm"
include "cn.mm"
include "3nn.mm"
include "a1i.mm"
include "cneg.mm"
include "cioo.mm"
include "cxr.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "neg1rr.mm"
include "rexri.mm"
include "1re.mm"
include "halfre.mm"
include "3pm3.2i.mm"
include "cc0.mm"
include "neg1lt0.mm"
include "halfgt0.mm"
include "pm3.2i.mm"
include "0re.mm"
include "lttri.mm"
include "ax-mp.mm"
include "halflt1.mm"
include "elioo3g.mm"
include "mpbir.mm"
include "knoppcn2.mm"
include "trud.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "2cn.mm"
include "mulid2i.mm"
include "2lt3.mm"
include "eqbrtri.mm"
include "wb.mm"
include "2pos.mm"
include "nnrei.mm"
include "2re.mm"
include "ltmuldivi.mm"
include "mpbi.mm"
include "cle.mm"
include "ltleii.mm"
include "absidi.mm"
include "oveq2i.mm"
include "nncni.mm"
include "2ne0.mm"
include "divreci.mm"
include "eqcomi.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "knoppndv.mm"

theorem cnndvlem1
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cW: class W
  assume cnndvlem1.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume cnndvlem1.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( ( 1 / 2 ) ^ n ) x. ( T ` ( ( ( 2 x. 3 ) ^ n ) x. y ) ) ) ) )
  assume cnndvlem1.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )

  disjoint F i
  disjoint F w
  disjoint i w
  disjoint T n
  disjoint T y
  disjoint n y
  disjoint i n
  disjoint i y
  disjoint n w
  disjoint w y
  disjoint i x
  disjoint w x
  assert |- ( W e. ( RR -cn-> RR ) /\ dom ( RR _D W ) = (/) )

  proof
    cW
    cr
    cr
    ccncf
    co
    wcel
    #
    cr
    cW
    cdv
    co
    cdm
    c0
    wceq
    #
    @0
    wtru
    vx
    vy
    vw
    c1
    c2
    cdiv
    co
    #
    cT
    vi
    vn
    cF
    c3
    cW
    cnndvlem1.t
    cnndvlem1.f
    cnndvlem1.w
    c3
    cn
    wcel
    wtru
    3nn
    a1i
    #
    @2
    c1
    cneg
    #
    c1
    cioo
    co
    wcel
    #
    wtru
    @5
    @4
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    w3a
    #
    @4
    @2
    clt
    wbr
    #
    @2
    c1
    clt
    wbr
    #
    wa
    #
    wa
    @9
    @12
    @6
    @7
    @8
    @4
    neg1rr
    rexri
    c1
    1re
    rexri
    @2
    halfre
    rexri
    3pm3.2i
    @10
    @11
    @4
    cc0
    clt
    wbr
    #
    cc0
    @2
    clt
    wbr
    #
    wa
    @10
    @13
    @14
    neg1lt0
    halfgt0
    pm3.2i
    @4
    cc0
    @2
    neg1rr
    0re
    halfre
    lttri
    ax-mp
    halflt1
    pm3.2i
    pm3.2i
    @4
    c1
    @2
    elioo3g
    mpbir
    a1i
    #
    knoppcn2
    trud
    @1
    wtru
    vx
    vy
    vw
    @2
    cT
    vi
    vn
    cF
    c3
    cW
    cnndvlem1.t
    cnndvlem1.f
    cnndvlem1.w
    @15
    @3
    c1
    c3
    @2
    cabs
    cfv
    #
    cmul
    co
    #
    clt
    wbr
    wtru
    c1
    c3
    c2
    cdiv
    co
    #
    @17
    clt
    c1
    c2
    cmul
    co
    #
    c3
    clt
    wbr
    #
    c1
    @18
    clt
    wbr
    #
    @19
    c2
    c3
    clt
    c2
    2cn
    mulid2i
    2lt3
    eqbrtri
    cc0
    c2
    clt
    wbr
    @20
    @21
    wb
    2pos
    c1
    c3
    c2
    1re
    c3
    3nn
    nnrei
    2re
    ltmuldivi
    ax-mp
    mpbi
    @17
    c3
    @2
    cmul
    co
    #
    @18
    @16
    @2
    c3
    cmul
    cc0
    @2
    cle
    wbr
    @16
    @2
    wceq
    cc0
    @2
    0re
    halfre
    halfgt0
    ltleii
    @2
    halfre
    absidi
    ax-mp
    oveq2i
    @18
    @22
    c3
    c2
    c3
    3nn
    nncni
    2cn
    2ne0
    divreci
    eqcomi
    eqtri
    breqtrri
    a1i
    knoppndv
    trud
    pm3.2i
end
