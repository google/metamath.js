include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp1d.mm"

theorem hlne1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume ishlg.g: |- ( ph -> G e. V )
  assume hlcomd.1: |- ( ph -> A ( K ` C ) B )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    cA
    cC
    cB
    cI
    co
    wcel
    cB
    cC
    cA
    cI
    co
    wcel
    wo
    #
    wph
    cA
    cB
    cC
    cK
    cfv
    wbr
    @0
    @1
    @2
    w3a
    hlcomd.1
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cV
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.b
    ishlg.c
    ishlg.g
    ishlg
    mpbid
    simp1d
end
