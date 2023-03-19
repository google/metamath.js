include "coppc.mm"
include "cfv.mm"
include "cinv.mm"
include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cmon.mm"
include "eqid.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "oppcmon.mm"
include "eleqtrrd.mm"
include "oppcsect.mm"
include "mpbird.mm"
include "monsect.mm"
include "oppcinv.mm"
include "breqd.mm"
include "mpbid.mm"

theorem episect
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume sectepi.b: |- B = ( Base ` C )
  assume sectepi.e: |- E = ( Epi ` C )
  assume sectepi.s: |- S = ( Sect ` C )
  assume sectepi.c: |- ( ph -> C e. Cat )
  assume sectepi.x: |- ( ph -> X e. B )
  assume sectepi.y: |- ( ph -> Y e. B )
  assume episect.n: |- N = ( Inv ` C )
  assume episect.1: |- ( ph -> F e. ( X E Y ) )
  assume episect.2: |- ( ph -> F ( X S Y ) G )


  assert |- ( ph -> F ( X N Y ) G )

  proof
    wph
    cF
    cG
    cY
    cX
    cC
    coppc
    cfv
    #
    cinv
    cfv
    #
    co
    #
    wbr
    cF
    cG
    cX
    cY
    cN
    co
    #
    wbr
    wph
    cB
    @0
    @0
    csect
    cfv
    #
    cF
    cG
    @0
    cmon
    cfv
    #
    @1
    cY
    cX
    cB
    cC
    @0
    @0
    eqid
    #
    sectepi.b
    oppcbas
    @5
    eqid
    #
    @4
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
    @6
    oppccat
    syl
    sectepi.y
    sectepi.x
    @1
    eqid
    #
    wph
    cF
    cX
    cY
    cE
    co
    cY
    cX
    @5
    co
    episect.1
    wph
    cC
    cE
    @5
    @0
    cY
    cX
    @6
    sectepi.c
    @7
    sectepi.e
    oppcmon
    eleqtrrd
    wph
    cG
    cF
    cX
    cY
    @4
    co
    wbr
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    episect.2
    wph
    cB
    cC
    cS
    @4
    cG
    cF
    @0
    cX
    cY
    sectepi.b
    @6
    sectepi.c
    sectepi.x
    sectepi.y
    sectepi.s
    @8
    oppcsect
    mpbird
    monsect
    wph
    @2
    @3
    cF
    cG
    wph
    cB
    cC
    cN
    @1
    @0
    cY
    cX
    sectepi.b
    @6
    sectepi.c
    sectepi.y
    sectepi.x
    episect.n
    @9
    oppcinv
    breqd
    mpbid
end
