include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "wf.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wss.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wi.mm"
include "i1f1lem.mm"
include "simpli.mm"
include "0re.mm"
include "1re.mm"
include "prssi.mm"
include "mp2an.mm"
include "fss.mm"
include "a1i.mm"
include "cfn.mm"
include "crn.mm"
include "prfi.mm"
include "cv.mm"
include "cif.mm"
include "1ex.mm"
include "prid2.mm"
include "c0ex.mm"
include "prid1.mm"
include "keepel.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "ssfi.mm"
include "sylancr.mm"
include "cdif.mm"
include "cun.mm"
include "ax-mp.mm"
include "df-pr.mm"
include "equncomi.mm"
include "sseqtri.mm"
include "ssdif.mm"
include "difun2.mm"
include "difss.mm"
include "eqsstri.mm"
include "sstri.mm"
include "sseli.mm"
include "elsni.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "simpri.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "simpll.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "simplr.mm"
include "i1fd.mm"

theorem i1f1
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume i1f1.1: |- F = ( x e. RR |-> if ( x e. A , 1 , 0 ) )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR ) -> F e. dom S.1 )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vy
    cF
    cr
    cr
    cF
    wf
    #
    @4
    cr
    cc0
    c1
    cpr
    #
    cF
    wf
    #
    @6
    cr
    wss
    #
    @5
    @7
    @1
    cF
    ccnv
    #
    c1
    csn
    #
    cima
    #
    cA
    wceq
    #
    wi
    #
    vx
    cA
    cF
    i1f1.1
    i1f1lem
    #
    simpli
    #
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @8
    0re
    1re
    cc0
    c1
    cr
    prssi
    mp2an
    cr
    @6
    cr
    cF
    fss
    mp2an
    a1i
    @4
    @6
    cfn
    wcel
    cF
    crn
    #
    @6
    wss
    #
    @16
    cfn
    wcel
    cc0
    c1
    prfi
    @4
    @7
    @17
    @4
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    @6
    cF
    @20
    @6
    wcel
    @4
    @18
    cr
    wcel
    wa
    @19
    c1
    cc0
    @6
    cc0
    c1
    1ex
    prid2
    cc0
    c1
    c0ex
    prid1
    keepel
    a1i
    i1f1.1
    fmptd
    cr
    @6
    cF
    frn
    #
    syl
    @6
    @16
    ssfi
    sylancr
    @4
    vy
    cv
    #
    @16
    cc0
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    @9
    @22
    csn
    #
    cima
    #
    cA
    @0
    @25
    @4
    @28
    @11
    cA
    @25
    @27
    @10
    @9
    @25
    @22
    c1
    @25
    @22
    @10
    wcel
    @22
    c1
    wceq
    @24
    @10
    @22
    @24
    @10
    @23
    cun
    #
    @23
    cdif
    #
    @10
    @16
    @29
    wss
    @24
    @30
    wss
    @16
    @6
    @29
    @7
    @17
    @15
    @21
    ax-mp
    @6
    @23
    @10
    cc0
    c1
    df-pr
    equncomi
    sseqtri
    @16
    @29
    @23
    ssdif
    ax-mp
    @30
    @10
    @23
    cdif
    @10
    @10
    @23
    difun2
    @10
    @23
    difss
    eqsstri
    sstri
    sseli
    @22
    c1
    elsni
    syl
    sneqd
    imaeq2d
    @1
    @12
    @3
    @7
    @13
    @14
    simpri
    adantr
    sylan9eqr
    #
    @1
    @3
    @25
    simpll
    eqeltrd
    @26
    @28
    cvol
    cfv
    @2
    cr
    @26
    @28
    cA
    cvol
    @31
    fveq2d
    @1
    @3
    @25
    simplr
    eqeltrd
    i1fd
end
