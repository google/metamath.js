include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "eldif.mm"
include "wne.mm"
include "cvv.mm"
include "csn.mm"
include "fvex.mm"
include "eldifsn.mm"
include "mpbiran.mm"
include "csupp.mm"
include "co.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "ibar.mm"
include "mp1i.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "sseld.mm"
include "sylbird.mm"
include "expdimp.mm"
include "syl5bir.mm"
include "necon1bd.mm"
include "impr.mm"
include "sylan2b.mm"

theorem suppssr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume suppssr.f: |- ( ph -> F : A --> B )
  assume suppssr.n: |- ( ph -> ( F supp Z ) C_ W )
  assume suppssr.a: |- ( ph -> A e. V )
  assume suppssr.z: |- ( ph -> Z e. U )


  assert |- ( ( ph /\ X e. ( A \ W ) ) -> ( F ` X ) = Z )

  proof
    cX
    cA
    cW
    cdif
    wcel
    wph
    cX
    cA
    wcel
    #
    cX
    cW
    wcel
    #
    wn
    #
    wa
    cX
    cF
    cfv
    #
    cZ
    wceq
    #
    cX
    cA
    cW
    eldif
    wph
    @0
    @2
    @4
    wph
    @0
    wa
    #
    @1
    @3
    cZ
    @3
    cZ
    wne
    #
    @3
    cvv
    cZ
    csn
    cdif
    wcel
    #
    @5
    @1
    @7
    @3
    cvv
    wcel
    #
    @6
    cX
    cF
    fvex
    #
    @3
    cvv
    cZ
    eldifsn
    #
    mpbiran
    wph
    @0
    @7
    @1
    wph
    @0
    @7
    wa
    #
    cX
    cF
    cZ
    csupp
    co
    #
    wcel
    #
    @1
    wph
    @13
    @0
    @6
    wa
    #
    @11
    wph
    cF
    cA
    wfn
    #
    cA
    cV
    wcel
    cZ
    cU
    wcel
    @13
    @14
    wb
    wph
    cA
    cB
    cF
    wf
    @15
    suppssr.f
    cA
    cB
    cF
    ffn
    syl
    suppssr.a
    suppssr.z
    cX
    cF
    cV
    cU
    cA
    cZ
    elsuppfn
    syl3anc
    wph
    @0
    @6
    @7
    @5
    @6
    @8
    @6
    wa
    #
    @7
    @8
    @6
    @16
    wb
    @5
    @9
    @8
    @6
    ibar
    mp1i
    @10
    syl6bbr
    pm5.32da
    bitrd
    wph
    @12
    cW
    cX
    suppssr.n
    sseld
    sylbird
    expdimp
    syl5bir
    necon1bd
    impr
    sylan2b
end
