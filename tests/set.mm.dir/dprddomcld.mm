include "cdm.mm"
include "wceq.mm"
include "cdprd.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "dprddomprc.mm"
include "sylbir.mm"
include "con4i.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "sylc.mm"

theorem dprddomcld
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  assume dprddomcld.1: |- ( ph -> G dom DProd S )
  assume dprddomcld.2: |- ( ph -> dom S = I )


  assert |- ( ph -> I e. _V )

  proof
    wph
    cS
    cdm
    #
    cI
    wceq
    #
    cG
    cS
    cdprd
    cdm
    wbr
    #
    cI
    cvv
    wcel
    #
    dprddomcld.2
    dprddomcld.1
    @2
    @0
    cvv
    wcel
    #
    @1
    @3
    @4
    @2
    @4
    wn
    @0
    cvv
    wnel
    @2
    wn
    @0
    cvv
    df-nel
    cS
    cG
    dprddomprc
    sylbir
    con4i
    @0
    cI
    cvv
    eleq1
    syl5ib
    sylc
end
