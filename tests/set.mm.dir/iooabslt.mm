include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "recnd.mm"
include "caddc.mm"
include "cioo.mm"
include "cr.mm"
include "elioore.mm"
include "syl.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "wbr.mm"
include "cbl.mm"
include "wa.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "bl2ioo.mm"
include "eleqtrrd.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "a1i.mm"
include "elind.mm"
include "rexrd.mm"
include "blres.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "wb.mm"
include "elbl.mm"
include "mpbid.mm"
include "simprd.mm"
include "eqbrtrrd.mm"

theorem iooabslt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iooabslt.1: |- ( ph -> A e. RR )
  assume iooabslt.2: |- ( ph -> B e. RR )
  assume iooabslt.3: |- ( ph -> C e. ( ( A - B ) (,) ( A + B ) ) )


  assert |- ( ph -> ( abs ` ( A - C ) ) < B )

  proof
    wph
    cA
    cC
    cabs
    cmin
    ccom
    #
    co
    #
    cA
    cC
    cmin
    co
    cabs
    cfv
    #
    cB
    clt
    wph
    cA
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @1
    @2
    wceq
    wph
    cA
    iooabslt.1
    recnd
    #
    wph
    cC
    wph
    cC
    cA
    cB
    cmin
    co
    #
    cA
    cB
    caddc
    co
    #
    cioo
    co
    #
    wcel
    cC
    cr
    wcel
    #
    iooabslt.3
    cC
    @6
    @7
    elioore
    syl
    recnd
    cA
    cC
    @0
    @0
    eqid
    cnmetdval
    syl2anc
    wph
    @4
    @1
    cB
    clt
    wbr
    #
    wph
    cC
    cA
    cB
    @0
    cbl
    cfv
    co
    #
    wcel
    #
    @4
    @10
    wa
    #
    wph
    @12
    @9
    wph
    cC
    @11
    cr
    cin
    #
    wcel
    @12
    @9
    wa
    wph
    cC
    cA
    cB
    @0
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    @14
    wph
    cC
    @8
    @16
    iooabslt.3
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @16
    @8
    wceq
    iooabslt.1
    iooabslt.2
    cA
    cB
    @15
    @15
    eqid
    #
    bl2ioo
    syl2anc
    eleqtrrd
    wph
    @0
    cc
    cxmt
    cfv
    wcel
    #
    cA
    cc
    cr
    cin
    wcel
    cB
    cxr
    wcel
    #
    @16
    @14
    wceq
    @18
    wph
    cnxmet
    a1i
    #
    wph
    cc
    cr
    cA
    @5
    iooabslt.1
    elind
    wph
    cB
    iooabslt.2
    rexrd
    #
    @15
    @0
    cA
    cB
    cc
    cr
    @17
    blres
    syl3anc
    eleqtrd
    cC
    @11
    cr
    elin
    sylib
    simpld
    wph
    @18
    @3
    @19
    @12
    @13
    wb
    @20
    @5
    @21
    cC
    @0
    cA
    cB
    cc
    elbl
    syl3anc
    mpbid
    simprd
    eqbrtrrd
end
