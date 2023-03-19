include "cxp.mm"
include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
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
include "cop.mm"
include "c1st.mm"
include "c2nd.mm"
include "eqcomi.mm"
include "pm3.2i.mm"
include "eqop.mm"
include "mpbiri.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "isclwlke.mm"
include "sylan9bbr.mm"

theorem clwlkcomp
  let cP: class P
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume isclwlke.v: |- V = ( Vtx ` G )
  assume isclwlke.i: |- I = ( iEdg ` G )
  assume clwlkcomp.1: |- F = ( 1st ` W )
  assume clwlkcomp.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint I k
  disjoint V k
  assert |- ( ( G e. X /\ W e. ( S X. T ) ) -> ( W e. ( ClWalks ` G ) <-> ( ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) /\ ( A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) ) )

  proof
    cW
    cS
    cT
    cxp
    wcel
    #
    cW
    cG
    cclwlks
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
    cX
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
    wa
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
    cc0
    cP
    cfv
    @4
    cP
    cfv
    wceq
    wa
    wa
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
    clwlkcomp.1
    eqcomi
    cP
    @12
    clwlkcomp.2
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
    cX
    isclwlke.v
    isclwlke.i
    isclwlke
    sylan9bbr
end
