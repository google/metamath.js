include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "ccnv.mm"
include "fzto1stfv1.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "wceq.mm"
include "fzto1st.mm"
include "symgbasf1o.mm"
include "syl.mm"
include "cuz.mm"
include "cfz.mm"
include "co.mm"
include "elfzuz2.mm"
include "eleq2s.mm"
include "eluzfz1.mm"
include "syl6eleqr.mm"
include "f1ocnvfv1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem fzto1stinvn
  let cB: class B
  let cD: class D
  let cP: class P
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cN: class N
  let vx: setvar x
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  assume psgnfzto1st.d: |- D = ( 1 ... N )
  assume psgnfzto1st.p: |- P = ( i e. D |-> if ( i = 1 , I , if ( i <_ I , ( i - 1 ) , i ) ) )
  assume psgnfzto1st.g: |- G = ( SymGrp ` D )
  assume psgnfzto1st.b: |- B = ( Base ` G )

  disjoint D i
  disjoint I i
  disjoint N i
  disjoint B i
  disjoint D x
  disjoint i x
  disjoint K i
  disjoint K x
  disjoint B m
  disjoint B n
  disjoint i m
  disjoint m n
  disjoint i n
  disjoint D m
  disjoint D n
  disjoint I m
  disjoint N m
  disjoint N n
  disjoint P m
  assert |- ( I e. D -> ( `' P ` I ) = 1 )

  proof
    cI
    cD
    wcel
    #
    c1
    cP
    cfv
    #
    cP
    ccnv
    #
    cfv
    #
    cI
    @2
    cfv
    c1
    @0
    @1
    cI
    @2
    cD
    cP
    vi
    cI
    cN
    psgnfzto1st.d
    psgnfzto1st.p
    fzto1stfv1
    fveq2d
    @0
    cD
    cD
    cP
    wf1o
    #
    c1
    cD
    wcel
    #
    @3
    c1
    wceq
    @0
    cP
    cB
    wcel
    @4
    cB
    cD
    cP
    vi
    cG
    cI
    cN
    psgnfzto1st.d
    psgnfzto1st.p
    psgnfzto1st.g
    psgnfzto1st.b
    fzto1st
    cD
    cB
    cP
    cG
    psgnfzto1st.g
    psgnfzto1st.b
    symgbasf1o
    syl
    @0
    cN
    c1
    cuz
    cfv
    wcel
    #
    @5
    @6
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
    @6
    c1
    @7
    cD
    c1
    cN
    eluzfz1
    psgnfzto1st.d
    syl6eleqr
    syl
    cD
    cD
    c1
    cP
    f1ocnvfv1
    syl2anc
    eqtr3d
end
