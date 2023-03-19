include "csupp.mm"
include "co.mm"
include "cmpt.mm"
include "oveq1i.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "eldifi.mm"
include "adantl.mm"
include "wn.mm"
include "cvv.mm"
include "csn.mm"
include "ccnv.mm"
include "cima.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "suppimacnv.mm"
include "eleq2d.mm"
include "wb.mm"
include "elpreima.mm"
include "syl.mm"
include "bitrd.mm"
include "baibd.mm"
include "notbid.mm"
include "biimpd.mm"
include "expimpd.mm"
include "eldif.mm"
include "wne.mm"
include "fvex.mm"
include "eldifsn.mm"
include "mpbiran.mm"
include "necon2bbii.mm"
include "3imtr4g.mm"
include "imp.mm"
include "syl3anc.mm"
include "suppss2.mm"
include "syl5eqss.mm"

theorem suppss3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume suppss3.1: |- G = ( x e. A |-> B )
  assume suppss3.a: |- ( ph -> A e. V )
  assume suppss3.z: |- ( ph -> Z e. W )
  assume suppss3.2: |- ( ph -> F Fn A )
  assume suppss3.3: |- ( ( ph /\ x e. A /\ ( F ` x ) = Z ) -> B = Z )

  disjoint A x
  disjoint F x
  disjoint Z x
  disjoint ph x
  assert |- ( ph -> ( G supp Z ) C_ ( F supp Z ) )

  proof
    wph
    cG
    cZ
    csupp
    co
    vx
    cA
    cB
    cmpt
    #
    cZ
    csupp
    co
    cF
    cZ
    csupp
    co
    #
    cG
    @0
    cZ
    csupp
    suppss3.1
    oveq1i
    wph
    cA
    cB
    vx
    cV
    @1
    cZ
    wph
    vx
    cv
    #
    cA
    @1
    cdif
    wcel
    #
    wa
    wph
    @2
    cA
    wcel
    #
    @2
    cF
    cfv
    #
    cZ
    wceq
    #
    cB
    cZ
    wceq
    wph
    @3
    simpl
    @3
    @4
    wph
    @2
    cA
    @1
    eldifi
    adantl
    wph
    @3
    @6
    wph
    @4
    @2
    @1
    wcel
    #
    wn
    #
    wa
    @5
    cvv
    cZ
    csn
    cdif
    #
    wcel
    #
    wn
    #
    @3
    @6
    wph
    @4
    @8
    @11
    wph
    @4
    wa
    #
    @8
    @11
    @12
    @7
    @10
    wph
    @7
    @4
    @10
    wph
    @7
    @2
    cF
    ccnv
    @9
    cima
    #
    wcel
    #
    @4
    @10
    wa
    #
    wph
    @1
    @13
    @2
    wph
    cF
    cvv
    wcel
    #
    cZ
    cW
    wcel
    @1
    @13
    wceq
    wph
    cF
    cA
    wfn
    #
    cA
    cV
    wcel
    @16
    suppss3.2
    suppss3.a
    cA
    cV
    cF
    fnex
    syl2anc
    suppss3.z
    cF
    cvv
    cW
    cZ
    suppimacnv
    syl2anc
    eleq2d
    wph
    @17
    @14
    @15
    wb
    suppss3.2
    cA
    @2
    @9
    cF
    elpreima
    syl
    bitrd
    baibd
    notbid
    biimpd
    expimpd
    @2
    cA
    @1
    eldif
    @10
    @5
    cZ
    @10
    @5
    cvv
    wcel
    @5
    cZ
    wne
    @2
    cF
    fvex
    @5
    cvv
    cZ
    eldifsn
    mpbiran
    necon2bbii
    3imtr4g
    imp
    suppss3.3
    syl3anc
    suppss3.a
    suppss2
    syl5eqss
end
