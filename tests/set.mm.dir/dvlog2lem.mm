include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "cxmt.mm"
include "cxr.mm"
include "wss.mm"
include "cnxmet.mm"
include "ax-1cn.mm"
include "1re.mm"
include "rexri.mm"
include "blssm.mm"
include "mp3an.mm"
include "eqsstri.mm"
include "sseli.mm"
include "wn.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "1m0e1.mm"
include "cr.mm"
include "mnfxr.mm"
include "0re.mm"
include "iocssre.mm"
include "mp2an.mm"
include "a1i.mm"
include "w3a.mm"
include "wb.mm"
include "elioc2.mm"
include "simp3bi.mm"
include "lesub2dd.mm"
include "syl5eqbrr.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "sylancr.mm"
include "0le1.mm"
include "letrd.mm"
include "abssubge0d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "cme.mm"
include "cnmet.mm"
include "metcl.mm"
include "syl3anc.mm"
include "lenlt.mm"
include "mpbid.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "mtbird.mm"
include "con2i.mm"
include "eleq2s.mm"
include "eldifd.mm"
include "ssriv.mm"

theorem dvlog2lem
  let cS: class S
  let vx: setvar x
  assume dvlog2.s: |- S = ( 1 ( ball ` ( abs o. - ) ) 1 )


  assert |- S C_ ( CC \ ( -oo (,] 0 ) )

  proof
    vx
    cS
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    vx
    cv
    #
    cS
    wcel
    @1
    cc
    @0
    cS
    cc
    @1
    cS
    c1
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cc
    dvlog2.s
    @2
    cc
    cxmt
    cfv
    wcel
    #
    c1
    cc
    wcel
    #
    c1
    cxr
    wcel
    #
    @3
    cc
    wss
    cnxmet
    ax-1cn
    c1
    1re
    rexri
    #
    @2
    c1
    c1
    cc
    blssm
    mp3an
    eqsstri
    sseli
    @1
    @0
    wcel
    #
    wn
    @1
    @3
    cS
    @8
    @1
    @3
    wcel
    #
    @8
    @9
    c1
    @1
    @2
    co
    #
    c1
    clt
    wbr
    #
    @8
    c1
    @10
    cle
    wbr
    #
    @11
    wn
    #
    @8
    c1
    c1
    @1
    cmin
    co
    #
    @10
    cle
    @8
    c1
    c1
    cc0
    cmin
    co
    @14
    cle
    1m0e1
    @8
    @1
    cc0
    c1
    @0
    cr
    @1
    cmnf
    cxr
    wcel
    #
    cc0
    cr
    wcel
    #
    @0
    cr
    wss
    mnfxr
    0re
    cmnf
    cc0
    iocssre
    mp2an
    #
    sseli
    #
    @16
    @8
    0re
    a1i
    #
    c1
    cr
    wcel
    #
    @8
    1re
    a1i
    #
    @8
    @1
    cr
    wcel
    #
    cmnf
    @1
    clt
    wbr
    #
    @1
    cc0
    cle
    wbr
    #
    @15
    @16
    @8
    @22
    @23
    @24
    w3a
    wb
    mnfxr
    0re
    cmnf
    cc0
    @1
    elioc2
    mp2an
    simp3bi
    #
    lesub2dd
    syl5eqbrr
    @8
    @10
    @14
    cabs
    cfv
    #
    @14
    @8
    @5
    @1
    cc
    wcel
    #
    @10
    @26
    wceq
    ax-1cn
    @0
    cc
    @1
    @0
    cr
    cc
    @17
    ax-resscn
    sstri
    sseli
    #
    c1
    @1
    @2
    @2
    eqid
    cnmetdval
    sylancr
    @8
    @1
    c1
    @18
    @21
    @8
    @1
    cc0
    c1
    @18
    @19
    @21
    @25
    cc0
    c1
    cle
    wbr
    @8
    0le1
    a1i
    letrd
    abssubge0d
    eqtrd
    breqtrrd
    @8
    @20
    @10
    cr
    wcel
    #
    @12
    @13
    wb
    1re
    @8
    @2
    cc
    cme
    cfv
    wcel
    #
    @5
    @27
    @29
    @30
    @8
    cnmet
    a1i
    @5
    @8
    ax-1cn
    a1i
    #
    @28
    c1
    @1
    @2
    cc
    metcl
    syl3anc
    c1
    @10
    lenlt
    sylancr
    mpbid
    @8
    @4
    @6
    @5
    @27
    @9
    @11
    wb
    @4
    @8
    cnxmet
    a1i
    @6
    @8
    @7
    a1i
    @31
    @28
    @1
    @2
    c1
    c1
    cc
    elbl2
    syl22anc
    mtbird
    con2i
    dvlog2.s
    eleq2s
    eldifd
    ssriv
end
