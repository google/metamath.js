include "cop.mm"
include "cdm.mm"
include "wcel.mm"
include "cxp.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cpo.mm"
include "wceq.mm"
include "wa.mm"
include "clat.mm"
include "islat.mm"
include "sylib.mm"
include "simprl.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "simprrd.mm"
include "jca.mm"

theorem latcl2
  let wph: wff ph
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latcl2.b: |- B = ( Base ` K )
  assume latcl2.j: |- .\/ = ( join ` K )
  assume latcl2.m: |- ./\ = ( meet ` K )
  assume latcl2.k: |- ( ph -> K e. Lat )
  assume latcl2.x: |- ( ph -> X e. B )
  assume latcl2.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( <. X , Y >. e. dom .\/ /\ <. X , Y >. e. dom ./\ ) )

  proof
    wph
    cX
    cY
    cop
    #
    c.or
    cdm
    #
    wcel
    @0
    c.an
    cdm
    #
    wcel
    wph
    @0
    cB
    cB
    cxp
    #
    @1
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @0
    @3
    wcel
    latcl2.x
    latcl2.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    #
    wph
    cK
    cpo
    wcel
    #
    @1
    @3
    wceq
    #
    @2
    @3
    wceq
    #
    wa
    wa
    #
    @6
    wph
    cK
    clat
    wcel
    @8
    latcl2.k
    cB
    c.or
    cK
    c.an
    latcl2.b
    latcl2.j
    latcl2.m
    islat
    sylib
    #
    @5
    @6
    @7
    simprl
    syl
    eleqtrrd
    wph
    @0
    @3
    @2
    @4
    wph
    @5
    @6
    @7
    @9
    simprrd
    eleqtrrd
    jca
end
