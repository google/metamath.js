include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cwun.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "1strwun.mm"
include "syldan.mm"

theorem setc1strwun
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cX: class X
  assume setc1strwun.s: |- S = ( SetCat ` U )
  assume setc1strwun.c: |- C = ( Base ` S )
  assume setc1strwun.u: |- ( ph -> U e. WUni )
  assume setc1strwun.o: |- ( ph -> _om e. U )


  assert |- ( ( ph /\ X e. C ) -> { <. ( Base ` ndx ) , X >. } e. U )

  proof
    wph
    cX
    cC
    wcel
    #
    cX
    cU
    wcel
    #
    cnx
    cbs
    cfv
    cX
    cop
    csn
    #
    cU
    wcel
    wph
    @0
    @1
    wph
    cC
    cU
    cX
    wph
    cU
    cS
    cbs
    cfv
    cC
    wph
    cS
    cU
    cwun
    setc1strwun.s
    setc1strwun.u
    setcbas
    setc1strwun.c
    syl6reqr
    eleq2d
    biimpa
    wph
    cX
    cU
    @2
    @2
    eqid
    setc1strwun.u
    setc1strwun.o
    1strwun
    syldan
end
