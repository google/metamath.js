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
include "cn0.mm"
include "lencl.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "cz.mm"
include "nn0z.mm"
include "fzval3.mm"
include "syl.mm"
include "feq2d.mm"
include "biimpa.mm"
include "iswrdi.mm"
include "sylan.mm"
include "3adant3.mm"
include "adantr.mm"

theorem clwlksf1clwwlklem3
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
  assert |- ( W e. C -> ( 2nd ` W ) e. Word ( Vtx ` G ) )

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
    #
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
    #
    cG
    cvtx
    cfv
    #
    cW
    c2nd
    cfv
    #
    wf
    #
    cc0
    @6
    cfv
    @3
    @6
    cfv
    wceq
    #
    w3a
    #
    @3
    cN
    wceq
    #
    wa
    @6
    @5
    cword
    wcel
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
    @9
    @11
    @10
    @2
    @7
    @11
    @8
    @2
    @3
    cn0
    wcel
    #
    @7
    @11
    @1
    @0
    lencl
    @12
    @7
    wa
    cc0
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @5
    @6
    wf
    #
    @11
    @12
    @7
    @15
    @12
    @4
    @14
    @5
    @6
    @12
    @3
    cz
    wcel
    @4
    @14
    wceq
    @3
    nn0z
    cc0
    @3
    fzval3
    syl
    feq2d
    biimpa
    @5
    @13
    @6
    iswrdi
    syl
    sylan
    3adant3
    adantr
    syl
end
