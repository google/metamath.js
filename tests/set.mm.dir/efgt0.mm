include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "reefcl.mm"
include "cc0.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cle.mm"
include "rehalfcl.mm"
include "reefcld.mm"
include "sqge0d.mm"
include "cmul.mm"
include "cc.mm"
include "cz.mm"
include "wceq.mm"
include "recnd.mm"
include "2z.mm"
include "efexp.mm"
include "sylancl.mm"
include "recn.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2.mm"
include "mp3an23.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "efne0.mm"
include "ne0gt0d.mm"

theorem efgt0
  let cA: class A


  assert |- ( A e. RR -> 0 < ( exp ` A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    ce
    cfv
    #
    cA
    reefcl
    @0
    cc0
    cA
    c2
    cdiv
    co
    #
    ce
    cfv
    #
    c2
    cexp
    co
    #
    @1
    cle
    @0
    @3
    @0
    @2
    cA
    rehalfcl
    #
    reefcld
    sqge0d
    @0
    c2
    @2
    cmul
    co
    #
    ce
    cfv
    #
    @4
    @1
    @0
    @2
    cc
    wcel
    c2
    cz
    wcel
    @7
    @4
    wceq
    @0
    @2
    @5
    recnd
    2z
    @2
    c2
    efexp
    sylancl
    @0
    @6
    cA
    ce
    @0
    cA
    cc
    wcel
    #
    @6
    cA
    wceq
    #
    cA
    recn
    #
    @8
    c2
    cc
    wcel
    c2
    cc0
    wne
    @9
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    syl
    fveq2d
    eqtr3d
    breqtrd
    @0
    @8
    @1
    cc0
    wne
    @10
    cA
    efne0
    syl
    ne0gt0d
end
