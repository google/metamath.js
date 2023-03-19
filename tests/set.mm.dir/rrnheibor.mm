include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccmp.mm"
include "cms.mm"
include "cfv.mm"
include "ctotbnd.mm"
include "ccld.mm"
include "cbnd.mm"
include "cme.mm"
include "crrn.mm"
include "rrnmet.mm"
include "cxp.mm"
include "cres.mm"
include "metres2.mm"
include "syl5eqel.mm"
include "sylan.mm"
include "biantrurd.mm"
include "heibor.mm"
include "syl6bb.mm"
include "eleq1i.mm"
include "wb.mm"
include "rrncms.mm"
include "adantr.mm"
include "cmetss.mm"
include "syl.mm"
include "syl5bb.mm"
include "rrntotbnd.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem rrnheibor
  let cT: class T
  let cU: class U
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  assume rrnheibor.1: |- X = ( RR ^m I )
  assume rrnheibor.2: |- M = ( ( Rn ` I ) |` ( Y X. Y ) )
  assume rrnheibor.3: |- T = ( MetOpen ` M )
  assume rrnheibor.4: |- U = ( MetOpen ` ( Rn ` I ) )


  assert |- ( ( I e. Fin /\ Y C_ X ) -> ( T e. Comp <-> ( Y e. ( Clsd ` U ) /\ M e. ( Bnd ` Y ) ) ) )

  proof
    cI
    cfn
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cT
    ccmp
    wcel
    #
    cM
    cY
    cms
    cfv
    #
    wcel
    #
    cM
    cY
    ctotbnd
    cfv
    wcel
    #
    wa
    #
    cY
    cU
    ccld
    cfv
    wcel
    #
    cM
    cY
    cbnd
    cfv
    wcel
    #
    wa
    @2
    @3
    cM
    cY
    cme
    cfv
    #
    wcel
    #
    @3
    wa
    @7
    @2
    @11
    @3
    @0
    cI
    crrn
    cfv
    #
    cX
    cme
    cfv
    wcel
    #
    @1
    @11
    cI
    cX
    rrnheibor.1
    rrnmet
    @13
    @1
    wa
    cM
    @12
    cY
    cY
    cxp
    cres
    #
    @10
    rrnheibor.2
    @12
    cY
    cX
    metres2
    syl5eqel
    sylan
    biantrurd
    cM
    cT
    cY
    rrnheibor.3
    heibor
    syl6bb
    @2
    @5
    @8
    @6
    @9
    @5
    @14
    @4
    wcel
    #
    @2
    @8
    cM
    @14
    @4
    rrnheibor.2
    eleq1i
    @2
    @12
    cX
    cms
    cfv
    wcel
    #
    @15
    @8
    wb
    @0
    @16
    @1
    cI
    cX
    rrnheibor.1
    rrncms
    adantr
    @12
    cU
    cX
    cY
    rrnheibor.4
    cmetss
    syl
    syl5bb
    @0
    @6
    @9
    wb
    @1
    cI
    cM
    cX
    cY
    rrnheibor.1
    rrnheibor.2
    rrntotbnd
    adantr
    anbi12d
    bitrd
end
