include "cun.mm"
include "cdm.mm"
include "cuni.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "caragenelss.mm"
include "unssd.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "elpwi.mm"
include "adantl.mm"
include "caragenuncllem.mm"
include "carageneld.mm"

theorem caragenuncl
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cF: class F
  let cO: class O
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragenuncl.1: |- ( ph -> O e. OutMeas )
  assume caragenuncl.2: |- S = ( CaraGen ` O )
  assume caragenuncl.3: |- ( ph -> E e. S )
  assume caragenuncl.4: |- ( ph -> F e. S )


  assert |- ( ph -> ( E u. F ) e. S )

  proof
    wph
    cS
    cE
    cF
    cun
    #
    cO
    cO
    cdm
    cuni
    #
    va
    caragenuncl.1
    @1
    eqid
    #
    caragenuncl.2
    wph
    @0
    @1
    cpw
    #
    wcel
    #
    @0
    @1
    wss
    #
    wph
    cE
    cF
    @1
    wph
    cE
    cS
    cO
    @1
    caragenuncl.1
    caragenuncl.2
    caragenuncl.3
    @2
    caragenelss
    wph
    cF
    cS
    cO
    @1
    caragenuncl.1
    caragenuncl.2
    caragenuncl.4
    @2
    caragenelss
    unssd
    #
    wph
    @0
    cvv
    wcel
    #
    @4
    @5
    wb
    wph
    @5
    @1
    cvv
    wcel
    @7
    @6
    wph
    cO
    come
    @1
    caragenuncl.1
    @2
    unidmex
    @0
    @1
    cvv
    ssexg
    syl2anc
    @0
    @1
    cvv
    elpwg
    syl
    mpbird
    wph
    va
    cv
    #
    @3
    wcel
    #
    wa
    @8
    cS
    cE
    cF
    cO
    @1
    wph
    cO
    come
    wcel
    @9
    caragenuncl.1
    adantr
    caragenuncl.2
    wph
    cE
    cS
    wcel
    @9
    caragenuncl.3
    adantr
    wph
    cF
    cS
    wcel
    @9
    caragenuncl.4
    adantr
    @2
    @9
    @8
    @1
    wss
    wph
    @8
    @1
    elpwi
    adantl
    caragenuncllem
    carageneld
end
