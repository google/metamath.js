include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "wb.mm"
include "elfz1.mm"
include "3anass.mm"
include "ibar.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "wn.mm"
include "c0.mm"
include "cxp.mm"
include "cpw.mm"
include "fzf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "eleq2d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "simpl.mm"
include "pm5.21ni.mm"
include "pm2.61i.mm"
include "3bitr4ri.mm"

theorem elfz2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) <-> ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) /\ ( M <_ K /\ K <_ N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cK
    cz
    wcel
    #
    wa
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    wa
    #
    wa
    @2
    @3
    @7
    wa
    #
    wa
    #
    @0
    @1
    @3
    w3a
    #
    @7
    wa
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @2
    @3
    @7
    anass
    @10
    @4
    @7
    @0
    @1
    @3
    df-3an
    anbi1i
    @2
    @12
    @9
    wb
    @2
    @12
    @3
    @5
    @6
    w3a
    #
    @9
    cK
    cM
    cN
    elfz1
    @13
    @8
    @2
    @9
    @3
    @5
    @6
    3anass
    @2
    @8
    ibar
    syl5bb
    bitrd
    @2
    wn
    #
    @12
    cK
    c0
    wcel
    #
    @9
    @14
    @11
    c0
    cK
    cM
    cN
    cz
    cfz
    cz
    cz
    cxp
    cz
    cpw
    cfz
    fzf
    fdmi
    ndmov
    eleq2d
    @15
    @2
    @9
    @15
    @2
    cK
    noel
    pm2.21i
    @2
    @8
    simpl
    pm5.21ni
    bitrd
    pm2.61i
    3bitr4ri
end
