include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "fveq2d.mm"
include "c1.mm"
include "cvv.mm"
include "wcel.mm"
include "tpex.mm"
include "a1i.mm"
include "df-base.mm"
include "1nn.mm"
include "strndxid.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "fvexd.mm"
include "w3a.mm"
include "slotsbhcdif.mm"
include "3simpa.mm"
include "mp1i.mm"
include "fvtp1g.mm"
include "syl21anc.mm"
include "3eqtr2rd.mm"

theorem estrreslem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cH: class H
  let cV: class V
  assume estrres.c: |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )
  assume estrres.b: |- ( ph -> B e. V )


  assert |- ( ph -> B = ( Base ` C ) )

  proof
    wph
    cC
    cbs
    cfv
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    #
    cnx
    cco
    cfv
    #
    c.x
    cop
    #
    ctp
    #
    cbs
    cfv
    @0
    @6
    cfv
    #
    cB
    wph
    cC
    @6
    cbs
    estrres.c
    fveq2d
    wph
    @6
    cbs
    c1
    cvv
    @6
    cvv
    wcel
    wph
    @1
    @3
    @5
    tpex
    a1i
    df-base
    1nn
    strndxid
    wph
    @0
    cvv
    wcel
    cB
    cV
    wcel
    @0
    @2
    wne
    #
    @0
    @4
    wne
    #
    wa
    #
    @7
    cB
    wceq
    wph
    cnx
    cbs
    fvexd
    estrres.b
    @8
    @9
    @2
    @4
    wne
    #
    w3a
    @10
    wph
    slotsbhcdif
    @8
    @9
    @11
    3simpa
    mp1i
    @0
    @2
    @4
    cB
    cH
    c.x
    cvv
    cV
    fvtp1g
    syl21anc
    3eqtr2rd
end
