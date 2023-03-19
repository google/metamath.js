include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "id.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "breqtrd.mm"
include "cfz.mm"
include "simpllr.mm"
include "syl6eleq.mm"
include "elfzle1.mm"
include "syl.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnred.mm"
include "1red.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "simplr.mm"
include "pm2.21dd.mm"
include "eqidd.mm"
include "ifeqda.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem fzto1st1
  let cD: class D
  let cP: class P
  let vi: setvar i
  let cI: class I
  let cN: class N
  let vx: setvar x
  let cK: class K
  assume psgnfzto1st.d: |- D = ( 1 ... N )
  assume psgnfzto1st.p: |- P = ( i e. D |-> if ( i = 1 , I , if ( i <_ I , ( i - 1 ) , i ) ) )

  disjoint D i
  disjoint I i
  disjoint N i
  disjoint D x
  disjoint i x
  disjoint K i
  disjoint K x
  assert |- ( I = 1 -> P = ( _I |` D ) )

  proof
    cI
    c1
    wceq
    #
    vi
    cD
    vi
    cv
    #
    c1
    wceq
    #
    cI
    @1
    cI
    cle
    wbr
    #
    @1
    c1
    cmin
    co
    #
    @1
    cif
    #
    cif
    #
    cmpt
    vi
    cD
    @1
    cmpt
    #
    cP
    cid
    cD
    cres
    #
    @0
    vi
    cD
    @6
    @1
    @0
    @1
    cD
    wcel
    #
    wa
    #
    @2
    cI
    @5
    @1
    @10
    @2
    wa
    cI
    c1
    @1
    @0
    @0
    @9
    @2
    @0
    id
    #
    ad2antrr
    @10
    @2
    simpr
    eqtr4d
    @10
    @2
    wn
    #
    wa
    #
    @3
    @4
    @1
    @1
    @13
    @3
    wa
    #
    @2
    @4
    @1
    wceq
    @14
    @2
    @1
    c1
    cle
    wbr
    c1
    @1
    cle
    wbr
    #
    @14
    @1
    cI
    c1
    cle
    @13
    @3
    simpr
    @0
    @0
    @9
    @12
    @3
    @11
    ad3antrrr
    breqtrd
    @14
    @1
    c1
    cN
    cfz
    co
    #
    wcel
    @15
    @14
    @1
    cD
    @16
    @0
    @9
    @12
    @3
    simpllr
    psgnfzto1st.d
    syl6eleq
    #
    @1
    c1
    cN
    elfzle1
    syl
    @14
    @1
    c1
    @14
    @1
    @14
    @16
    cn
    @1
    cN
    fz1ssnn
    @17
    sseldi
    nnred
    @14
    1red
    letri3d
    mpbir2and
    @10
    @12
    @3
    simplr
    pm2.21dd
    @13
    @3
    wn
    wa
    @1
    eqidd
    ifeqda
    ifeqda
    mpteq2dva
    psgnfzto1st.p
    @7
    @8
    vi
    cD
    mptresid
    eqcomi
    3eqtr4g
end
