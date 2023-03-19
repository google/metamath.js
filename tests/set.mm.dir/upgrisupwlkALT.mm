include "cupgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cupwlks.mm"
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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "wb.mm"
include "upgrwlkupwlkb.mm"
include "3ad2ant1.mm"
include "isupwlk.mm"
include "bitrd.mm"

theorem upgrisupwlkALT
  let cP: class P
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  assume upgrisupwlkALT.v: |- V = ( Vtx ` G )
  assume upgrisupwlkALT.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  disjoint k x
  assert |- ( ( G e. UPGraph /\ F e. U /\ P e. Z ) -> ( F ( Walks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cU
    wcel
    #
    cP
    cZ
    wcel
    #
    w3a
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cP
    cG
    cupwlks
    cfv
    wbr
    #
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
    cF
    cfv
    cI
    cfv
    @6
    cP
    cfv
    @6
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @5
    cfzo
    co
    wral
    w3a
    @0
    @1
    @3
    @4
    wb
    @2
    cP
    cF
    cG
    upgrwlkupwlkb
    3ad2ant1
    cP
    cU
    vk
    cF
    cG
    cI
    cV
    cupgr
    cZ
    upgrisupwlkALT.v
    upgrisupwlkALT.i
    isupwlk
    bitrd
end
