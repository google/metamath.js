include "cmpt.mm"
include "ccom.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "mptex2.mm"
include "sseldd.mm"
include "ex.mm"
include "ralrimi.mm"
include "eqidd.mm"
include "fmptcof.mm"
include "eqcomd.mm"
include "cc.mm"
include "cncfrss.mm"
include "cncfss.mm"
include "syl2anc.mm"
include "cncfco.mm"
include "eqeltrd.mm"

theorem cncfcompt2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let vk: setvar k
  assume cncfcompt2.xph: |- F/ x ph
  assume cncfcompt2.ab: |- ( ph -> ( x e. A |-> R ) e. ( A -cn-> B ) )
  assume cncfcompt2.cd: |- ( ph -> ( y e. C |-> S ) e. ( C -cn-> E ) )
  assume cncfcompt2.bc: |- ( ph -> B C_ C )
  assume cncfcompt2.st: |- ( y = R -> S = T )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint C y
  disjoint x y
  disjoint R y
  disjoint S x
  disjoint T y
  disjoint k x
  assert |- ( ph -> ( x e. A |-> T ) e. ( A -cn-> E ) )

  proof
    wph
    vx
    cA
    cT
    cmpt
    #
    vy
    cC
    cS
    cmpt
    #
    vx
    cA
    cR
    cmpt
    #
    ccom
    #
    cA
    cE
    ccncf
    co
    wph
    @3
    @0
    wph
    vx
    vy
    cA
    cC
    cR
    cS
    cT
    @2
    @1
    wph
    cR
    cC
    wcel
    #
    vx
    cA
    cncfcompt2.xph
    wph
    vx
    cv
    cA
    wcel
    #
    @4
    wph
    @5
    wa
    cB
    cC
    cR
    wph
    cB
    cC
    wss
    #
    @5
    cncfcompt2.bc
    adantr
    wph
    vx
    cA
    cR
    cB
    wph
    @2
    cA
    cB
    ccncf
    co
    #
    wcel
    cA
    cB
    @2
    wf
    cncfcompt2.ab
    cA
    cB
    @2
    cncff
    syl
    mptex2
    sseldd
    ex
    ralrimi
    wph
    @2
    eqidd
    wph
    @1
    eqidd
    cncfcompt2.st
    fmptcof
    eqcomd
    wph
    cA
    cC
    cE
    @2
    @1
    wph
    @7
    cA
    cC
    ccncf
    co
    #
    @2
    wph
    @6
    cC
    cc
    wss
    #
    @7
    @8
    wss
    cncfcompt2.bc
    wph
    @1
    cC
    cE
    ccncf
    co
    wcel
    @9
    cncfcompt2.cd
    cC
    cE
    @1
    cncfrss
    syl
    cA
    cB
    cC
    cncfss
    syl2anc
    cncfcompt2.ab
    sseldd
    cncfcompt2.cd
    cncfco
    eqeltrd
end
