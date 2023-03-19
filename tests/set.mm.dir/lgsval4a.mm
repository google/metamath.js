include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cseq.mm"
include "wne.mm"
include "wceq.mm"
include "simpl.mm"
include "nnz.mm"
include "adantl.mm"
include "nnne0.mm"
include "lgsval4.mm"
include "syl3anc.mm"
include "wn.mm"
include "nngt0.mm"
include "cr.mm"
include "wi.mm"
include "0re.mm"
include "nnre.mm"
include "ltnsym.mm"
include "sylancr.mm"
include "mpd.mm"
include "intnanrd.mm"
include "iffalsed.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "cv.mm"
include "cfz.mm"
include "lgsfcl3.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "zmulcl.mm"
include "seqcl.mm"
include "zcnd.mm"
include "mulid2d.mm"
include "3eqtrd.mm"

theorem lgsval4a
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  assume lgsval4.1: |- F = ( n e. NN |-> if ( n e. Prime , ( ( A /L n ) ^ ( n pCnt N ) ) , 1 ) )

  disjoint A n
  disjoint N n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint P n
  assert |- ( ( A e. ZZ /\ N e. NN ) -> ( A /L N ) = ( seq 1 ( x. , F ) ` N ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    clgs
    co
    #
    cN
    cc0
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    cN
    cabs
    cfv
    #
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    c1
    cN
    @10
    cfv
    #
    cmul
    co
    @13
    @2
    @0
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    @3
    @12
    wceq
    @0
    @1
    simpl
    #
    @1
    @14
    @0
    cN
    nnz
    adantl
    #
    @1
    @15
    @0
    cN
    nnne0
    adantl
    #
    cA
    vn
    cF
    cN
    lgsval4.1
    lgsval4
    syl3anc
    @2
    @8
    c1
    @11
    @13
    cmul
    @2
    @6
    @7
    c1
    @2
    @4
    @5
    @2
    cc0
    cN
    clt
    wbr
    #
    @4
    wn
    #
    @1
    @19
    @0
    cN
    nngt0
    adantl
    @2
    cc0
    cr
    wcel
    cN
    cr
    wcel
    #
    @19
    @20
    wi
    0re
    @1
    @21
    @0
    cN
    nnre
    adantl
    #
    cc0
    cN
    ltnsym
    sylancr
    mpd
    intnanrd
    iffalsed
    @2
    @9
    cN
    @10
    @2
    cN
    @22
    @2
    cN
    @1
    cN
    cn0
    wcel
    @0
    cN
    nnnn0
    adantl
    nn0ge0d
    absidd
    fveq2d
    oveq12d
    @2
    @13
    @2
    @13
    @2
    vx
    vy
    cmul
    cz
    cF
    c1
    cN
    @2
    cN
    cn
    c1
    cuz
    cfv
    @0
    @1
    simpr
    nnuz
    syl6eleq
    @2
    cn
    cz
    cF
    wf
    #
    vx
    cv
    #
    cn
    wcel
    @24
    cF
    cfv
    cz
    wcel
    @24
    c1
    cN
    cfz
    co
    wcel
    @2
    @0
    @14
    @15
    @23
    @16
    @17
    @18
    cA
    vn
    cF
    cN
    lgsval4.1
    lgsfcl3
    syl3anc
    @24
    cN
    elfznn
    cn
    cz
    @24
    cF
    ffvelrn
    syl2an
    @24
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    @24
    @25
    cmul
    co
    cz
    wcel
    @2
    @24
    @25
    zmulcl
    adantl
    seqcl
    zcnd
    mulid2d
    3eqtrd
end
