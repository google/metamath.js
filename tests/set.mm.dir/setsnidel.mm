include "cop.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wcel.mm"
include "wne.mm"
include "elexd.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "wa.mm"
include "wb.mm"
include "opelresg.mm"
include "syl.mm"
include "mpbir2and.mm"
include "elun1.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "setsval.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"

theorem setsnidel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume setsidel.s: |- ( ph -> S e. V )
  assume setsidel.b: |- ( ph -> B e. W )
  assume setsidel.r: |- R = ( S sSet <. A , B >. )
  assume setsnidel.c: |- ( ph -> C e. X )
  assume setsnidel.d: |- ( ph -> D e. Y )
  assume setsnidel.s: |- ( ph -> <. C , D >. e. S )
  assume setsnidel.n: |- ( ph -> A =/= C )


  assert |- ( ph -> <. C , D >. e. R )

  proof
    wph
    cC
    cD
    cop
    #
    cS
    cvv
    cA
    csn
    cdif
    #
    cres
    #
    cA
    cB
    cop
    #
    csn
    #
    cun
    #
    cR
    wph
    @0
    @2
    wcel
    #
    @0
    @5
    wcel
    wph
    @6
    @0
    cS
    wcel
    #
    cC
    @1
    wcel
    #
    setsnidel.s
    wph
    cC
    cvv
    wcel
    cC
    cA
    wne
    @8
    wph
    cC
    cX
    setsnidel.c
    elexd
    wph
    cA
    cC
    setsnidel.n
    necomd
    cC
    cvv
    cA
    eldifsn
    sylanbrc
    wph
    cD
    cY
    wcel
    @6
    @7
    @8
    wa
    wb
    setsnidel.d
    cC
    cD
    cS
    @1
    cY
    opelresg
    syl
    mpbir2and
    @0
    @2
    @4
    elun1
    syl
    wph
    cR
    cS
    @3
    csts
    co
    #
    @5
    setsidel.r
    wph
    cS
    cV
    wcel
    cB
    cW
    wcel
    @9
    @5
    wceq
    setsidel.s
    setsidel.b
    cA
    cB
    cS
    cV
    cW
    setsval
    syl2anc
    syl5eq
    eleqtrrd
end
