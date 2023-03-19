include "cxp.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "cop.mm"
include "c1st.mm"
include "c2nd.mm"
include "wa.mm"
include "eqcomi.mm"
include "pm3.2i.mm"
include "eqop.mm"
include "mpbiri.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "iswlkg.mm"
include "sylan9bbr.mm"

theorem wlkcomp
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  assume wlkcomp.v: |- V = ( Vtx ` G )
  assume wlkcomp.i: |- I = ( iEdg ` G )
  assume wlkcomp.1: |- F = ( 1st ` W )
  assume wlkcomp.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( ( G e. U /\ W e. ( S X. T ) ) -> ( W e. ( Walks ` G ) <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) ) )

  proof
    cW
    cS
    cT
    cxp
    wcel
    #
    cW
    cG
    cwlks
    cfv
    #
    wcel
    #
    cF
    cP
    @1
    wbr
    #
    cG
    cU
    wcel
    cF
    cI
    cdm
    cword
    wcel
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    vk
    cv
    #
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @5
    cF
    cfv
    cI
    cfv
    #
    @6
    csn
    wceq
    @6
    @7
    cpr
    @8
    wss
    wif
    vk
    cc0
    @4
    cfzo
    co
    wral
    w3a
    @0
    @2
    cF
    cP
    cop
    #
    @1
    wcel
    @3
    @0
    cW
    @9
    @1
    @0
    cW
    @9
    wceq
    cW
    c1st
    cfv
    #
    cF
    wceq
    #
    cW
    c2nd
    cfv
    #
    cP
    wceq
    #
    wa
    @11
    @13
    cF
    @10
    wlkcomp.1
    eqcomi
    cP
    @12
    wlkcomp.2
    eqcomi
    pm3.2i
    cW
    cF
    cP
    cS
    cT
    eqop
    mpbiri
    eleq1d
    cF
    cP
    @1
    df-br
    syl6bbr
    cP
    vk
    cF
    cG
    cI
    cV
    cU
    wlkcomp.v
    wlkcomp.i
    iswlkg
    sylan9bbr
end
