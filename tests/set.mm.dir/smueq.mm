include "cn0.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfzo.mm"
include "cin.mm"
include "eqid.mm"
include "smueqlem.mm"

theorem smueq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vi: setvar i
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  assume smueq.a: |- ( ph -> A C_ NN0 )
  assume smueq.b: |- ( ph -> B C_ NN0 )
  assume smueq.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( A smul B ) i^i ( 0 ..^ N ) ) = ( ( ( A i^i ( 0 ..^ N ) ) smul ( B i^i ( 0 ..^ N ) ) ) i^i ( 0 ..^ N ) ) )

  proof
    wph
    cA
    cB
    vp
    vm
    cn0
    cpw
    #
    cn0
    vp
    cv
    #
    vm
    cv
    #
    cA
    wcel
    #
    vn
    cv
    #
    @2
    cmin
    co
    #
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    vn
    cn0
    @4
    cc0
    wceq
    c0
    @4
    c1
    cmin
    co
    cif
    cmpt
    #
    cc0
    cseq
    #
    vp
    vm
    @0
    cn0
    @1
    @3
    @5
    cB
    cc0
    cN
    cfzo
    co
    cin
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    @6
    cc0
    cseq
    #
    vm
    vn
    cN
    vp
    smueq.a
    smueq.b
    smueq.n
    @7
    eqid
    @8
    eqid
    smueqlem
end
