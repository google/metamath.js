include "coppc.mm"
include "cfv.mm"
include "cmon.mm"
include "co.mm"
include "csect.mm"
include "eqid.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "wbr.mm"
include "oppcsect.mm"
include "mpbird.mm"
include "sectmon.mm"
include "oppcmon.mm"
include "eleqtrd.mm"

theorem sectepi
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume sectepi.b: |- B = ( Base ` C )
  assume sectepi.e: |- E = ( Epi ` C )
  assume sectepi.s: |- S = ( Sect ` C )
  assume sectepi.c: |- ( ph -> C e. Cat )
  assume sectepi.x: |- ( ph -> X e. B )
  assume sectepi.y: |- ( ph -> Y e. B )
  assume sectepi.1: |- ( ph -> F ( X S Y ) G )


  assert |- ( ph -> G e. ( Y E X ) )

  proof
    wph
    cG
    cX
    cY
    cC
    coppc
    cfv
    #
    cmon
    cfv
    #
    co
    cY
    cX
    cE
    co
    wph
    cB
    @0
    @0
    csect
    cfv
    #
    cG
    cF
    @1
    cX
    cY
    cB
    cC
    @0
    @0
    eqid
    #
    sectepi.b
    oppcbas
    @1
    eqid
    #
    @2
    eqid
    #
    wph
    cC
    ccat
    wcel
    @0
    ccat
    wcel
    sectepi.c
    cC
    @0
    @3
    oppccat
    syl
    sectepi.x
    sectepi.y
    wph
    cG
    cF
    cX
    cY
    @2
    co
    wbr
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    sectepi.1
    wph
    cB
    cC
    cS
    @2
    cG
    cF
    @0
    cX
    cY
    sectepi.b
    @3
    sectepi.c
    sectepi.x
    sectepi.y
    sectepi.s
    @5
    oppcsect
    mpbird
    sectmon
    wph
    cC
    cE
    @1
    @0
    cX
    cY
    @3
    sectepi.c
    @4
    sectepi.e
    oppcmon
    eleqtrd
end
