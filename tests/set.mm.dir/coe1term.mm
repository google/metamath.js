include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "ccoe.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "wne.mm"
include "cdgr.mm"
include "wi.mm"
include "coe1termlem.mm"
include "simpld.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem coe1term
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume coe1term.1: |- F = ( z e. CC |-> ( A x. ( z ^ N ) ) )

  disjoint A z
  disjoint N z
  disjoint k n
  disjoint k z
  disjoint A k
  disjoint n z
  disjoint A n
  disjoint M n
  disjoint N k
  disjoint N n
  assert |- ( ( A e. CC /\ N e. NN0 /\ M e. NN0 ) -> ( ( coeff ` F ) ` M ) = if ( M = N , A , 0 ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    w3a
    #
    cM
    cF
    ccoe
    cfv
    #
    cfv
    #
    cM
    vn
    cn0
    vn
    cv
    #
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cM
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    @0
    @1
    @5
    @10
    wceq
    @2
    @0
    @1
    wa
    #
    cM
    @4
    @9
    @13
    @4
    @9
    wceq
    cA
    cc0
    wne
    cF
    cdgr
    cfv
    cN
    wceq
    wi
    vz
    cA
    vn
    cF
    cN
    coe1term.1
    coe1termlem
    simpld
    fveq1d
    3adant3
    @3
    @2
    @12
    cc
    wcel
    #
    @10
    @12
    wceq
    @0
    @1
    @2
    simp3
    @3
    @0
    cc0
    cc
    wcel
    @14
    @0
    @1
    @2
    simp1
    0cn
    @11
    cA
    cc0
    cc
    ifcl
    sylancl
    vn
    cM
    @8
    @12
    cn0
    cc
    @9
    @6
    cM
    wceq
    @7
    @11
    cA
    cc0
    @6
    cM
    cN
    eqeq1
    ifbid
    @9
    eqid
    fvmptg
    syl2anc
    eqtrd
end
