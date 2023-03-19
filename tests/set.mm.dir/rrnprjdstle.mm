include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cle.mm"
include "wcel.mm"
include "wceq.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "remetdval.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "cfn.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "elmapd.mm"
include "mpbird.mm"
include "crrx.mm"
include "cbs.mm"
include "rrxbasefi.mm"
include "rrxbase.mm"
include "syl.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "rrxdstprj1.mm"
include "syl22anc.mm"
include "eqbrtrd.mm"

theorem rrnprjdstle
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  assume rrnprjdstle.x: |- ( ph -> X e. Fin )
  assume rrnprjdstle.f: |- ( ph -> F : X --> RR )
  assume rrnprjdstle.g: |- ( ph -> G : X --> RR )
  assume rrnprjdstle.i: |- ( ph -> I e. X )
  assume rrnprjdstle.d: |- D = ( dist ` ( RR^ ` X ) )


  assert |- ( ph -> ( abs ` ( ( F ` I ) - ( G ` I ) ) ) <_ ( F D G ) )

  proof
    wph
    cI
    cF
    cfv
    #
    cI
    cG
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    @0
    @1
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    co
    #
    cF
    cG
    cD
    co
    #
    cle
    wph
    @4
    @2
    wph
    @0
    cr
    wcel
    @1
    cr
    wcel
    @4
    @2
    wceq
    wph
    cX
    cr
    cI
    cF
    rrnprjdstle.f
    rrnprjdstle.i
    ffvelrnd
    wph
    cX
    cr
    cI
    cG
    rrnprjdstle.g
    rrnprjdstle.i
    ffvelrnd
    @0
    @1
    @3
    @3
    eqid
    #
    remetdval
    syl2anc
    eqcomd
    wph
    cX
    cfn
    wcel
    #
    cI
    cX
    wcel
    cF
    vh
    cv
    cc0
    cfsupp
    wbr
    vh
    cr
    cX
    cmap
    co
    #
    crab
    #
    wcel
    cG
    @9
    wcel
    @4
    @5
    cle
    wbr
    rrnprjdstle.x
    rrnprjdstle.i
    wph
    cF
    @8
    @9
    wph
    cF
    @8
    wcel
    cX
    cr
    cF
    wf
    rrnprjdstle.f
    wph
    cr
    cX
    cF
    cvv
    cfn
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    rrnprjdstle.x
    elmapd
    mpbird
    wph
    cX
    crrx
    cfv
    #
    cbs
    cfv
    #
    @8
    @9
    wph
    @12
    @11
    cX
    rrnprjdstle.x
    @11
    eqid
    #
    @12
    eqid
    #
    rrxbasefi
    wph
    @7
    @12
    @9
    wceq
    rrnprjdstle.x
    @12
    vh
    @11
    cX
    cfn
    @13
    @14
    rrxbase
    syl
    eqtr3d
    #
    eleqtrd
    wph
    cG
    @8
    @9
    wph
    cG
    @8
    wcel
    cX
    cr
    cG
    wf
    rrnprjdstle.g
    wph
    cr
    cX
    cG
    cvv
    cfn
    @10
    rrnprjdstle.x
    elmapd
    mpbird
    @15
    eleqtrd
    cI
    cD
    vh
    cF
    cG
    cX
    @3
    cfn
    @9
    @9
    eqid
    rrnprjdstle.d
    @6
    rrxdstprj1
    syl22anc
    eqbrtrd
end
