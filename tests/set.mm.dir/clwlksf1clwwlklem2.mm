include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "c2nd.mm"
include "wf.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "clwlksf1clwwlklem0.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "biimpcd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "syl.mm"

theorem clwlksf1clwwlklem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint W c
  disjoint C c
  disjoint F c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint W i
  assert |- ( W e. C -> ( ( 2nd ` W ) ` 0 ) = ( ( 2nd ` W ) ` N ) )

  proof
    cW
    cC
    wcel
    cW
    c1st
    cfv
    #
    cG
    ciedg
    cfv
    cdm
    cword
    wcel
    #
    cc0
    @0
    chash
    cfv
    #
    cfz
    co
    cG
    cvtx
    cfv
    cW
    c2nd
    cfv
    #
    wf
    #
    cc0
    @3
    cfv
    #
    @2
    @3
    cfv
    #
    wceq
    #
    w3a
    #
    @2
    cN
    wceq
    #
    wa
    @5
    cN
    @3
    cfv
    #
    wceq
    #
    cA
    cB
    cC
    cF
    cG
    cN
    cW
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem0
    @8
    @9
    @11
    @7
    @1
    @9
    @11
    wi
    @4
    @9
    @7
    @11
    @9
    @6
    @10
    @5
    @2
    cN
    @3
    fveq2
    eqeq2d
    biimpcd
    3ad2ant3
    imp
    syl
end
