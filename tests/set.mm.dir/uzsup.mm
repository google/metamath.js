include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cif.mm"
include "cuz.mm"
include "simpl.mm"
include "flcl.mm"
include "peano2zd.mm"
include "id.mm"
include "ifcl.mm"
include "syl2anr.mm"
include "zre.mm"
include "reflcl.mm"
include "peano2re.mm"
include "syl.mm"
include "max1.mm"
include "syl2an.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "syl6eleqr.mm"
include "simpr.mm"
include "adantl.mm"
include "zred.mm"
include "fllep1.mm"
include "max2.mm"
include "letrd.mm"
include "breq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wss.mm"
include "wb.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "ressxr.mm"
include "supxrunb1.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem uzsup
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  let vx: setvar x
  assume uzsup.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> sup ( Z , RR* , < ) = +oo )

  proof
    cM
    cz
    wcel
    #
    vx
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    #
    @0
    @4
    vx
    cr
    @0
    @1
    cr
    wcel
    #
    wa
    #
    cM
    @1
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @10
    cM
    cif
    #
    cZ
    wcel
    @1
    @12
    cle
    wbr
    #
    @4
    @8
    @12
    cM
    cuz
    cfv
    #
    cZ
    @8
    @0
    @12
    cz
    wcel
    #
    cM
    @12
    cle
    wbr
    #
    @12
    @14
    wcel
    @0
    @7
    simpl
    @7
    @10
    cz
    wcel
    @0
    @15
    @0
    @7
    @9
    @1
    flcl
    peano2zd
    @0
    id
    @11
    @10
    cM
    cz
    ifcl
    syl2anr
    #
    @0
    cM
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @16
    @7
    cM
    zre
    #
    @7
    @9
    cr
    wcel
    @19
    @1
    reflcl
    @9
    peano2re
    syl
    #
    cM
    @10
    max1
    syl2an
    cM
    @12
    eluz2
    syl3anbrc
    uzsup.1
    syl6eleqr
    @8
    @1
    @10
    @12
    @0
    @7
    simpr
    @7
    @19
    @0
    @21
    adantl
    @8
    @12
    @17
    zred
    @7
    @1
    @10
    cle
    wbr
    @0
    @1
    fllep1
    adantl
    @0
    @18
    @19
    @10
    @12
    cle
    wbr
    @7
    @20
    @21
    cM
    @10
    max2
    syl2an
    letrd
    @3
    @13
    vn
    @12
    cZ
    @2
    @12
    @1
    cle
    breq2
    rspcev
    syl2anc
    ralrimiva
    cZ
    cxr
    wss
    @5
    @6
    wb
    cZ
    cr
    cxr
    cZ
    cz
    cr
    cZ
    @14
    cz
    uzsup.1
    cM
    uzssz
    eqsstri
    zssre
    sstri
    ressxr
    sstri
    vx
    vn
    cZ
    supxrunb1
    ax-mp
    sylib
end
