include "cv.mm"
include "cn.mm"
include "wfn.mm"
include "cfv.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "caddc.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "eqid.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "simpld.mm"
include "adantll.mm"
include "simprd.mm"
include "ovoliun.mm"
include "ovoliunnfl.mm"

theorem ex-ovoliunnfl
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let vm: setvar m
  let vl: setvar l

  disjoint A x
  disjoint f n
  disjoint f m
  disjoint f l
  disjoint f x
  disjoint A f
  disjoint m n
  disjoint l n
  disjoint n x
  disjoint A n
  disjoint l m
  disjoint m x
  disjoint A m
  disjoint l x
  disjoint A l
  assert |- ( ( A ~<_ NN /\ A. x e. A x ~<_ NN ) -> U. A =/= RR )

  proof
    vx
    cA
    vf
    vm
    vn
    vf
    cv
    #
    cn
    wfn
    #
    vn
    cv
    #
    @0
    cfv
    #
    cr
    wss
    #
    @3
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    #
    wa
    vm
    cv
    #
    @0
    cfv
    #
    caddc
    vm
    cn
    @10
    covol
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    vm
    @12
    @13
    eqid
    @12
    eqid
    @8
    @9
    cn
    wcel
    #
    @10
    cr
    wss
    #
    @1
    @8
    @14
    wa
    #
    @15
    @11
    cr
    wcel
    #
    @7
    @15
    @17
    wa
    vn
    @9
    cn
    vn
    vm
    weq
    #
    @4
    @15
    @6
    @17
    @18
    @3
    @10
    cr
    @2
    @9
    @0
    fveq2
    #
    sseq1d
    @18
    @5
    @11
    cr
    @18
    @3
    @10
    covol
    @19
    fveq2d
    eleq1d
    anbi12d
    rspccva
    #
    simpld
    adantll
    @8
    @14
    @17
    @1
    @16
    @15
    @17
    @20
    simprd
    adantll
    ovoliun
    ovoliunnfl
end
