include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cv.mm"
include "cvdwm.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "cmul.mm"
include "caddc.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cc0.mm"
include "cmin.mm"
include "simpl.mm"
include "simpr.mm"
include "vdwlem13.mm"
include "ovex.mm"
include "simpllr.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "simpll.mm"
include "elmapg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "cuz.mm"
include "cfv.mm"
include "simplr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "vdwmc2.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem vdw
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cK: class K
  let va: setvar a
  let vc: setvar c
  let vd: setvar d

  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint K a
  disjoint c d
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint K c
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint K d
  disjoint f m
  disjoint f n
  disjoint K f
  disjoint m n
  disjoint K m
  disjoint K n
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R f
  disjoint R n
  assert |- ( ( R e. Fin /\ K e. NN0 ) -> E. n e. NN A. f e. ( R ^m ( 1 ... n ) ) E. c e. R E. a e. NN E. d e. NN A. m e. ( 0 ... ( K - 1 ) ) ( a + ( m x. d ) ) e. ( `' f " { c } ) )

  proof
    cR
    cfn
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cK
    vf
    cv
    #
    cvdwm
    wbr
    #
    vf
    cR
    c1
    vn
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    va
    cv
    vm
    cv
    vd
    cv
    cmul
    co
    caddc
    co
    @3
    ccnv
    vc
    cv
    csn
    cima
    wcel
    vm
    cc0
    cK
    c1
    cmin
    co
    cfz
    co
    wral
    vd
    cn
    wrex
    va
    cn
    wrex
    vc
    cR
    wrex
    #
    vf
    @7
    wral
    #
    vn
    cn
    wrex
    @2
    cR
    vf
    vn
    cK
    @0
    @1
    simpl
    @0
    @1
    simpr
    vdwlem13
    @2
    @8
    @10
    vn
    cn
    @2
    @5
    cn
    wcel
    #
    wa
    #
    @4
    @9
    vf
    @7
    @12
    @3
    @7
    wcel
    #
    wa
    #
    c1
    cR
    vm
    @3
    cK
    @6
    va
    vc
    vd
    c1
    @5
    cfz
    ovex
    #
    @0
    @1
    @11
    @13
    simpllr
    @12
    @13
    @6
    cR
    @3
    wf
    #
    @12
    @0
    @6
    cvv
    wcel
    @13
    @16
    wb
    @0
    @1
    @11
    simpll
    @15
    cR
    @6
    @3
    cfn
    cvv
    elmapg
    sylancl
    biimpa
    @14
    @5
    c1
    cuz
    cfv
    #
    wcel
    c1
    @6
    wcel
    @14
    @5
    cn
    @17
    @2
    @11
    @13
    simplr
    nnuz
    syl6eleq
    c1
    @5
    eluzfz1
    syl
    vdwmc2
    ralbidva
    rexbidva
    mpbid
end
