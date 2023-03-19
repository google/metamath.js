include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "c0.mm"
include "cfv.mm"
include "bnj645.mm"
include "wa.mm"
include "wfun.mm"
include "w3a.mm"
include "bnj334.mm"
include "bnj257.mm"
include "bitri.mm"
include "bnj345.mm"
include "bnj253.mm"
include "3bitri.mm"
include "simp1bi.mm"
include "bnj927.mm"
include "bnj930.mm"
include "syl.mm"
include "wss.mm"
include "cop.mm"
include "csn.mm"
include "bnj931.mm"
include "a1i.mm"
include "cdm.mm"
include "bnj268.mm"
include "bitr3i.mm"
include "fndm.mm"
include "bnj529.mm"
include "eleq2.mm"
include "biimpar.mm"
include "syl2anr.mm"
include "bnj1502.mm"
include "bnj918.mm"
include "bnj934.mm"
include "syl2anc.mm"

theorem bnj929
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwphn: wff ph"
  assume bnj929.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj929.4: |- ( ph' <-> [. p / n ]. ph )
  assume bnj929.7: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj929.10: |- D = ( _om \ { (/) } )
  assume bnj929.13: |- G = ( f u. { <. n , C >. } )
  assume bnj929.50: |- C e. _V

  disjoint A f
  disjoint A n
  disjoint f n
  disjoint R f
  disjoint R n
  disjoint X f
  disjoint X n
  assert |- ( ( n e. D /\ p = suc n /\ f Fn n /\ ph ) -> ph" )

  proof
    vn
    cv
    #
    cD
    wcel
    #
    vp
    cv
    #
    @0
    csuc
    wceq
    #
    vf
    cv
    #
    @0
    wfn
    #
    wph
    w-bnj17
    #
    wph
    c0
    cG
    cfv
    c0
    @4
    cfv
    wceq
    bnjwphn
    @1
    @3
    @5
    wph
    bnj645
    @6
    c0
    cG
    @4
    @6
    @3
    @5
    wa
    #
    cG
    wfun
    @6
    @7
    @1
    wph
    @6
    @5
    @1
    wph
    @3
    w-bnj17
    #
    @3
    @5
    @1
    wph
    w-bnj17
    @7
    @1
    wph
    w3a
    @6
    @5
    @1
    @3
    wph
    w-bnj17
    @8
    @1
    @3
    @5
    wph
    bnj334
    @5
    @1
    @3
    wph
    bnj257
    bitri
    @5
    @1
    wph
    @3
    bnj345
    @3
    @5
    @1
    wph
    bnj253
    3bitri
    simp1bi
    @7
    @2
    cG
    cC
    vf
    vn
    cG
    vp
    bnj929.13
    bnj929.50
    bnj927
    bnj930
    syl
    @4
    cG
    wss
    @6
    cG
    @4
    @0
    cC
    cop
    csn
    bnj929.13
    bnj931
    a1i
    @6
    @1
    @5
    wa
    #
    c0
    @4
    cdm
    #
    wcel
    #
    @6
    @9
    @3
    wph
    @6
    @1
    @5
    @3
    wph
    w-bnj17
    @9
    @3
    wph
    w3a
    @1
    @5
    @3
    wph
    bnj268
    @1
    @5
    @3
    wph
    bnj253
    bitr3i
    simp1bi
    @5
    @10
    @0
    wceq
    #
    c0
    @0
    wcel
    #
    @11
    @1
    @0
    @4
    fndm
    cD
    @0
    bnj929.10
    bnj529
    @12
    @11
    @13
    @10
    @0
    c0
    eleq2
    biimpar
    syl2anr
    syl
    bnj1502
    wph
    cA
    cR
    vf
    vn
    cG
    cX
    vp
    bnjwphm
    bnjwphn
    bnj929.1
    bnj929.4
    bnj929.7
    cC
    vf
    vn
    cG
    bnj929.13
    bnj918
    bnj934
    syl2anc
end
