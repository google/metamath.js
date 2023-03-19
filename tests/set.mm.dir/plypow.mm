include "cc.mm"
include "wss.mm"
include "c1.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "cply.mm"
include "cfv.mm"
include "wa.mm"
include "id.mm"
include "simp3.mm"
include "expcl.mm"
include "syl2anr.mm"
include "mulid2d.mm"
include "mpteq2dva.mm"
include "eqid.mm"
include "ply1term.mm"
include "eqeltrrd.mm"

theorem plypow
  let vz: setvar z
  let cS: class S
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cM: class M
  let wph: wff ph

  disjoint N z
  disjoint S z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint S k
  disjoint S x
  assert |- ( ( S C_ CC /\ 1 e. S /\ N e. NN0 ) -> ( z e. CC |-> ( z ^ N ) ) e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    c1
    cS
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    vz
    cc
    c1
    vz
    cv
    #
    cN
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    vz
    cc
    @5
    cmpt
    cS
    cply
    cfv
    @3
    vz
    cc
    @6
    @5
    @3
    @4
    cc
    wcel
    #
    wa
    @5
    @8
    @8
    @2
    @5
    cc
    wcel
    @3
    @8
    id
    @0
    @1
    @2
    simp3
    @4
    cN
    expcl
    syl2anr
    mulid2d
    mpteq2dva
    vz
    c1
    cS
    @7
    cN
    @7
    eqid
    ply1term
    eqeltrrd
end
