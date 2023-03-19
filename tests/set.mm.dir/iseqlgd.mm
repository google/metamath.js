include "cs3.mm"
include "ceqlg.mm"
include "cfv.mm"
include "wcel.mm"
include "ccgrg.mm"
include "wbr.mm"
include "eqid.mm"
include "trgcgr.mm"
include "iseqlg.mm"
include "mpbird.mm"

theorem iseqlgd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vx: setvar x
  let vg: setvar g
  assume iseqlg.p: |- P = ( Base ` G )
  assume iseqlg.m: |- .- = ( dist ` G )
  assume iseqlg.i: |- I = ( Itv ` G )
  assume iseqlg.l: |- L = ( LineG ` G )
  assume iseqlg.g: |- ( ph -> G e. TarskiG )
  assume iseqlg.a: |- ( ph -> A e. P )
  assume iseqlg.b: |- ( ph -> B e. P )
  assume iseqlg.c: |- ( ph -> C e. P )
  assume iseqlgd.1: |- ( ph -> ( A .- B ) = ( B .- C ) )
  assume iseqlgd.2: |- ( ph -> ( B .- C ) = ( C .- A ) )
  assume iseqlgd.3: |- ( ph -> ( C .- A ) = ( A .- B ) )


  assert |- ( ph -> <" A B C "> e. ( eqltrG ` G ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cG
    ceqlg
    cfv
    wcel
    @0
    cB
    cC
    cA
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    wph
    cA
    cB
    cC
    cB
    cP
    @1
    cC
    cA
    cG
    c.mi
    iseqlg.p
    iseqlg.m
    @1
    eqid
    iseqlg.g
    iseqlg.a
    iseqlg.b
    iseqlg.c
    iseqlg.b
    iseqlg.c
    iseqlg.a
    iseqlgd.1
    iseqlgd.2
    iseqlgd.3
    trgcgr
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    cL
    c.mi
    iseqlg.p
    iseqlg.m
    iseqlg.i
    iseqlg.l
    iseqlg.g
    iseqlg.a
    iseqlg.b
    iseqlg.c
    iseqlg
    mpbird
end
