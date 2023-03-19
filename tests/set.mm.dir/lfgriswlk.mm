include "wcel.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wa.mm"
include "cwlks.mm"
include "cword.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wne.mm"
include "cpr.mm"
include "wss.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wlkf.mm"
include "adantl.mm"
include "wlkp.mm"
include "wi.mm"
include "lfgrwlkprop.mm"
include "expcom.mm"
include "imp.mm"
include "wlkvtxeledg.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "3jca.mm"
include "wceq.mm"
include "csn.mm"
include "wif.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wn.mm"
include "wb.mm"
include "df-ne.mm"
include "ifpfal.mm"
include "sylbi.mm"
include "biimpar.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "iswlkg.mm"
include "ad2antrr.mm"
include "mpbir3and.mm"
include "impbida.mm"

theorem lfgriswlk
  let vx: setvar x
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  assume lfgrwlkprop.i: |- I = ( iEdg ` G )
  assume lfgriswlk.v: |- V = ( Vtx ` G )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint G k
  disjoint I k
  disjoint I x
  disjoint P k
  disjoint V k
  disjoint V x
  assert |- ( ( G e. W /\ I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } ) -> ( F ( Walks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( ( P ` k ) =/= ( P ` ( k + 1 ) ) /\ { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) ) )

  proof
    cG
    cW
    wcel
    #
    cI
    cdm
    #
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    cI
    wf
    #
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    @1
    cword
    wcel
    #
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
    wne
    #
    @9
    @10
    cpr
    @8
    cF
    cfv
    cI
    cfv
    #
    wss
    #
    wa
    #
    vk
    cc0
    @6
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @3
    @4
    wa
    #
    @5
    @7
    @16
    @4
    @5
    @3
    cP
    cF
    cG
    cI
    lfgrwlkprop.i
    wlkf
    adantl
    @4
    @7
    @3
    cP
    cF
    cG
    cV
    lfgriswlk.v
    wlkp
    adantl
    @18
    @11
    vk
    @15
    wral
    #
    @13
    vk
    @15
    wral
    #
    @16
    @3
    @4
    @19
    @2
    @4
    @19
    wi
    @0
    @4
    @2
    @19
    vx
    cP
    vk
    cF
    cG
    cI
    cV
    lfgrwlkprop.i
    lfgrwlkprop
    expcom
    adantl
    imp
    @4
    @20
    @3
    cP
    vk
    cF
    cG
    cI
    lfgrwlkprop.i
    wlkvtxeledg
    adantl
    @11
    @13
    vk
    @15
    r19.26
    sylanbrc
    3jca
    @3
    @17
    wa
    @4
    @5
    @7
    @9
    @10
    wceq
    #
    @12
    @9
    csn
    wceq
    #
    @13
    wif
    #
    vk
    @15
    wral
    #
    @3
    @5
    @7
    @16
    simpr1
    @3
    @5
    @7
    @16
    simpr2
    @17
    @24
    @3
    @16
    @5
    @24
    @7
    @14
    @23
    vk
    @15
    @11
    @23
    @13
    @11
    @21
    wn
    @23
    @13
    wb
    @9
    @10
    df-ne
    @21
    @22
    @13
    ifpfal
    sylbi
    biimpar
    ralimi
    3ad2ant3
    adantl
    @0
    @4
    @5
    @7
    @24
    w3a
    wb
    @2
    @17
    cP
    vk
    cF
    cG
    cI
    cV
    cW
    lfgriswlk.v
    lfgrwlkprop.i
    iswlkg
    ad2antrr
    mpbir3and
    impbida
end
