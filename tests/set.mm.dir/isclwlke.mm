include "cclwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "isclwlk.mm"
include "w3a.mm"
include "iswlkg.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl5bb.mm"

theorem isclwlke
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  assume isclwlke.v: |- V = ( Vtx ` G )
  assume isclwlke.i: |- I = ( iEdg ` G )

  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( G e. X -> ( F ( ClWalks ` G ) P <-> ( ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) /\ ( A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) ) )

  proof
    cF
    cP
    cG
    cclwlks
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    cF
    chash
    cfv
    #
    cP
    cfv
    wceq
    #
    wa
    #
    cG
    cX
    wcel
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    @1
    cfz
    co
    cV
    cP
    wf
    #
    wa
    #
    vk
    cv
    #
    cP
    cfv
    #
    @8
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @8
    cF
    cfv
    cI
    cfv
    #
    @9
    csn
    wceq
    @9
    @10
    cpr
    @11
    wss
    wif
    vk
    cc0
    @1
    cfzo
    co
    wral
    #
    @2
    wa
    wa
    #
    cP
    cF
    cG
    isclwlk
    @4
    @3
    @7
    @12
    wa
    #
    @2
    wa
    @13
    @4
    @0
    @14
    @2
    @4
    @0
    @5
    @6
    @12
    w3a
    @14
    cP
    vk
    cF
    cG
    cI
    cV
    cX
    isclwlke.v
    isclwlke.i
    iswlkg
    @5
    @6
    @12
    df-3an
    syl6bb
    anbi1d
    @7
    @12
    @2
    anass
    syl6bb
    syl5bb
end
