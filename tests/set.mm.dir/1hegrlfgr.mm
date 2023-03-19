include "csn.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "ciedg.mm"
include "wf.mm"
include "cop.mm"
include "wf1o.mm"
include "wcel.mm"
include "f1osng.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "cpr.mm"
include "prid1g.mm"
include "sseldd.mm"
include "prid2g.mm"
include "nehash2.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "fssd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem 1hegrlfgr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume 1hegrlfgr.a: |- ( ph -> A e. X )
  assume 1hegrlfgr.b: |- ( ph -> B e. V )
  assume 1hegrlfgr.c: |- ( ph -> C e. V )
  assume 1hegrlfgr.n: |- ( ph -> B =/= C )
  assume 1hegrlfgr.x: |- ( ph -> E e. ~P V )
  assume 1hegrlfgr.i: |- ( ph -> ( iEdg ` G ) = { <. A , E >. } )
  assume 1hegrlfgr.e: |- ( ph -> { B , C } C_ E )

  disjoint E x
  disjoint V x
  disjoint k x
  assert |- ( ph -> ( iEdg ` G ) : { A } --> { x e. ~P V | 2 <_ ( # ` x ) } )

  proof
    wph
    cA
    csn
    #
    c2
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    crab
    #
    cG
    ciedg
    cfv
    #
    wf
    @0
    @5
    cA
    cE
    cop
    csn
    #
    wf
    wph
    @0
    cE
    csn
    #
    @5
    @7
    wph
    @0
    @8
    @7
    wf1o
    #
    @0
    @8
    @7
    wf
    wph
    cA
    cX
    wcel
    cE
    @4
    wcel
    #
    @9
    1hegrlfgr.a
    1hegrlfgr.x
    cA
    cE
    cX
    @4
    f1osng
    syl2anc
    @0
    @8
    @7
    f1of
    syl
    wph
    cE
    @5
    wph
    @10
    c2
    cE
    chash
    cfv
    #
    cle
    wbr
    #
    cE
    @5
    wcel
    1hegrlfgr.x
    wph
    cB
    cC
    cE
    @4
    1hegrlfgr.x
    wph
    cB
    cC
    cpr
    #
    cE
    cB
    1hegrlfgr.e
    wph
    cB
    cV
    wcel
    cB
    @13
    wcel
    1hegrlfgr.b
    cB
    cC
    cV
    prid1g
    syl
    sseldd
    wph
    @13
    cE
    cC
    1hegrlfgr.e
    wph
    cC
    cV
    wcel
    cC
    @13
    wcel
    1hegrlfgr.c
    cB
    cC
    cV
    prid2g
    syl
    sseldd
    1hegrlfgr.n
    nehash2
    @3
    @12
    vx
    cE
    @4
    @1
    cE
    wceq
    @2
    @11
    c2
    cle
    @1
    cE
    chash
    fveq2
    breq2d
    elrab
    sylanbrc
    snssd
    fssd
    wph
    @0
    @5
    @6
    @7
    1hegrlfgr.i
    feq1d
    mpbird
end
