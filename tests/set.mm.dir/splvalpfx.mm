include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "chash.mm"
include "cfv.mm"
include "cpfx.mm"
include "splval.mm"
include "wceq.mm"
include "pfxval.mm"
include "3ad2antr1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem splvalpfx
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. V /\ ( F e. NN0 /\ T e. X /\ R e. Y ) ) -> ( S splice <. F , T , R >. ) = ( ( ( S prefix F ) ++ R ) ++ ( S substr <. T , ( # ` S ) >. ) ) )

  proof
    cS
    cV
    wcel
    #
    cF
    cn0
    wcel
    #
    cT
    cX
    wcel
    #
    cR
    cY
    wcel
    #
    w3a
    wa
    #
    cS
    cF
    cT
    cR
    cotp
    csplice
    co
    cS
    cc0
    cF
    cop
    csubstr
    co
    #
    cR
    cconcat
    co
    #
    cS
    cT
    cS
    chash
    cfv
    cop
    csubstr
    co
    #
    cconcat
    co
    cS
    cF
    cpfx
    co
    #
    cR
    cconcat
    co
    #
    @7
    cconcat
    co
    cR
    cS
    cT
    cF
    cV
    cn0
    cX
    cY
    splval
    @4
    @6
    @9
    @7
    cconcat
    @4
    @5
    @8
    cR
    cconcat
    @4
    @8
    @5
    @0
    @2
    @1
    @8
    @5
    wceq
    @3
    cS
    cF
    cV
    pfxval
    3ad2antr1
    eqcomd
    oveq1d
    oveq1d
    eqtrd
end
