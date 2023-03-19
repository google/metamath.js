include "crp.mm"
include "cq.mm"
include "cdif.mm"
include "wcel.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cdenom.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "crab.mm"
include "wss.mm"
include "cfn.mm"
include "wn.mm"
include "qnnen.mm"
include "nnenom.mm"
include "entri.mm"
include "pm3.2i.mm"
include "cr.mm"
include "wrex.mm"
include "wral.mm"
include "ssrab2.mm"
include "qssre.mm"
include "sstri.mm"
include "a1i.mm"
include "eldifi.mm"
include "rpred.mm"
include "eldifn.mm"
include "elrabi.mm"
include "nsyl.mm"
include "irrapxlem6.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "rencldnfi.mm"
include "syl31anc.mm"
include "jctil.mm"
include "ctbnfien.mm"
include "sylancr.mm"

theorem irrapx1
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vx: setvar x
  let vb: setvar b
  let cB: class B

  disjoint A y
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint A x
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint B y
  assert |- ( A e. ( RR+ \ QQ ) -> { y e. QQ | ( 0 < y /\ ( abs ` ( y - A ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ~~ NN )

  proof
    cA
    crp
    cq
    cdif
    wcel
    #
    cq
    com
    cen
    wbr
    #
    cn
    com
    cen
    wbr
    #
    wa
    cc0
    vy
    cv
    #
    clt
    wbr
    @3
    cA
    cmin
    co
    cabs
    cfv
    @3
    cdenom
    cfv
    c2
    cneg
    cexp
    co
    clt
    wbr
    wa
    #
    vy
    cq
    crab
    #
    cq
    wss
    #
    @5
    cfn
    wcel
    wn
    #
    wa
    @5
    cn
    cen
    wbr
    @1
    @2
    cq
    cn
    com
    qnnen
    nnenom
    entri
    nnenom
    pm3.2i
    @0
    @7
    @6
    @0
    @5
    cr
    wss
    #
    cA
    cr
    wcel
    cA
    @5
    wcel
    #
    wn
    vb
    cv
    cA
    cmin
    co
    cabs
    cfv
    va
    cv
    #
    clt
    wbr
    vb
    @5
    wrex
    #
    va
    crp
    wral
    @7
    @8
    @0
    @5
    cq
    cr
    @4
    vy
    cq
    ssrab2
    #
    qssre
    sstri
    a1i
    @0
    cA
    cA
    crp
    cq
    eldifi
    #
    rpred
    @0
    cA
    cq
    wcel
    @9
    cA
    crp
    cq
    eldifn
    @4
    vy
    cA
    cq
    elrabi
    nsyl
    @0
    @11
    va
    crp
    @0
    cA
    crp
    wcel
    @10
    crp
    wcel
    @11
    @13
    vb
    vy
    cA
    @10
    irrapxlem6
    sylan
    ralrimiva
    va
    vb
    @5
    cA
    rencldnfi
    syl31anc
    @12
    jctil
    @5
    cq
    cn
    ctbnfien
    sylancr
end
