include "cfv.mm"
include "wbr.mm"
include "hlcomb.mm"
include "mpbid.mm"

theorem hlcomd
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


  assert |- ( ph -> B ( K ` C ) A )

  proof
    wph
    cA
    cB
    cC
    cK
    cfv
    #
    wbr
    cB
    cA
    @0
    wbr
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
    hlcomb
    mpbid
end
