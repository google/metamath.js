include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "cmpt.mm"
include "a1i.mm"
include "iftrue.mm"
include "adantl.mm"
include "cuz.mm"
include "cfv.mm"
include "cfz.mm"
include "elfzuz2.mm"
include "eleq2s.mm"
include "eluzfz1.mm"
include "syl6eleqr.mm"
include "syl.mm"
include "id.mm"
include "fvmptd.mm"

theorem fzto1stfv1
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
  assert |- ( I e. D -> ( P ` 1 ) = I )

  proof
    cI
    cD
    wcel
    #
    vi
    c1
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
    @1
    c1
    cmin
    co
    @1
    cif
    #
    cif
    #
    cI
    cD
    cP
    cD
    cP
    vi
    cD
    @4
    cmpt
    wceq
    @0
    psgnfzto1st.p
    a1i
    @2
    @4
    cI
    wceq
    @0
    @2
    cI
    @3
    iftrue
    adantl
    @0
    cN
    c1
    cuz
    cfv
    wcel
    #
    c1
    cD
    wcel
    @5
    cI
    c1
    cN
    cfz
    co
    #
    cD
    cI
    c1
    cN
    elfzuz2
    psgnfzto1st.d
    eleq2s
    @5
    c1
    @6
    cD
    c1
    cN
    eluzfz1
    psgnfzto1st.d
    syl6eleqr
    syl
    @0
    id
    fvmptd
end
