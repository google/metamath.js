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
include "cle.mm"
include "wbr.mm"
include "clwlksf1clwwlklem0.mm"
include "wi.mm"
include "cn0.mm"
include "wfn.mm"
include "lencl.mm"
include "ffn.mm"
include "c1.mm"
include "caddc.mm"
include "nn0re.mm"
include "lep1d.mm"
include "adantr.mm"
include "fnfz0hash.mm"
include "breqtrrd.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "imp.mm"
include "syl.mm"

theorem clwlksf1clwwlklem1
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
  assert |- ( W e. C -> N <_ ( # ` ( 2nd ` W ) ) )

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
    cN
    @6
    chash
    cfv
    #
    cle
    wbr
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
    @10
    @12
    @2
    @7
    @10
    @12
    wi
    #
    @8
    @2
    @3
    cn0
    wcel
    #
    @6
    @4
    wfn
    #
    @13
    @7
    @1
    @0
    lencl
    @4
    @5
    @6
    ffn
    @14
    @15
    wa
    #
    @3
    @11
    cle
    wbr
    @10
    @12
    @16
    @3
    @3
    c1
    caddc
    co
    #
    @11
    cle
    @14
    @3
    @17
    cle
    wbr
    @15
    @14
    @3
    @3
    nn0re
    lep1d
    adantr
    @6
    @3
    fnfz0hash
    breqtrrd
    @3
    cN
    @11
    cle
    breq1
    syl5ibcom
    syl2an
    3adant3
    imp
    syl
end
