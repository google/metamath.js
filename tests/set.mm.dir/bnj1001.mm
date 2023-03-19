include "w-bnj17.mm"
include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "simplbi.mm"
include "bnj708.mm"
include "wfn.mm"
include "bnj1232.mm"
include "bnj706.mm"
include "bnj923.mm"
include "syl.mm"
include "elnn.mm"
include "syl2anc.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "simp3bi.mm"
include "bnj707.mm"
include "word.mm"
include "nnord.mm"
include "ordsucelsuc.mm"
include "3syl.mm"
include "biimpa.mm"
include "eleq2.mm"
include "anim12i.mm"
include "syl21anc.mm"
include "bianir.mm"
include "3jca.mm"

theorem bnj1001
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let bnjwchn: wff ch"
  assume bnj1001.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1001.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj1001.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj1001.13: |- D = ( _om \ { (/) } )
  assume bnj1001.27: |- ( ( th /\ ch /\ ta /\ et ) -> ch" )


  assert |- ( ( th /\ ch /\ ta /\ et ) -> ( ch" /\ i e. _om /\ suc i e. p ) )

  proof
    wth
    wch
    wta
    wet
    w-bnj17
    #
    bnjwchn
    vi
    cv
    #
    com
    wcel
    #
    @1
    csuc
    #
    vp
    cv
    #
    wcel
    #
    bnj1001.27
    @0
    @1
    vn
    cv
    #
    wcel
    #
    @6
    com
    wcel
    #
    @2
    wth
    wch
    wta
    wet
    @7
    wet
    @7
    vy
    cv
    @1
    vf
    cv
    #
    cfv
    wcel
    bnj1001.6
    simplbi
    bnj708
    #
    @0
    @6
    cD
    wcel
    #
    @8
    wth
    wch
    wta
    wet
    @11
    wch
    @11
    @9
    @6
    wfn
    wph
    wps
    bnj1001.3
    bnj1232
    bnj706
    #
    cD
    vn
    bnj1001.13
    bnj923
    #
    syl
    @1
    @6
    elnn
    syl2anc
    @0
    @3
    @6
    csuc
    #
    wcel
    #
    @5
    @15
    wb
    #
    wa
    #
    @5
    @0
    @11
    @7
    @4
    @14
    wceq
    #
    @17
    @12
    @10
    wth
    wch
    wta
    wet
    @18
    wta
    vm
    cv
    #
    com
    wcel
    @6
    @19
    csuc
    wceq
    @18
    bnj1001.5
    simp3bi
    bnj707
    @11
    @7
    wa
    @15
    @18
    @16
    @11
    @7
    @15
    @11
    @8
    @6
    word
    @7
    @15
    wb
    @13
    @6
    nnord
    @1
    @6
    ordsucelsuc
    3syl
    biimpa
    @4
    @14
    @3
    eleq2
    anim12i
    syl21anc
    @15
    @5
    bianir
    syl
    3jca
end
