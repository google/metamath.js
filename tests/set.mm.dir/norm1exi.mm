include "cv.mm"
include "c0v.mm"
include "wne.mm"
include "wrex.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "neeq1.mm"
include "cbvrexv.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "csm.mm"
include "cc.mm"
include "cr.mm"
include "chil.mm"
include "sheli.mm"
include "normcl.mm"
include "syl.mm"
include "adantr.mm"
include "cc0.mm"
include "wb.mm"
include "normne0.mm"
include "biimpar.mm"
include "rereccld.mm"
include "recnd.mm"
include "simpl.mm"
include "csh.mm"
include "shmulcl.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "norm1.mm"
include "sylan.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "rexlimiva.mm"
include "wn.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "norm-i.mm"
include "necon3bbid.mm"
include "syl5ib.mm"
include "reximia.mm"
include "sylib.mm"
include "impbii.mm"
include "bitri.mm"

theorem norm1exi
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let vz: setvar z
  assume norm1ex.1: |- H e. SH

  disjoint H x
  disjoint H y
  disjoint x z
  disjoint H z
  disjoint y z
  assert |- ( E. x e. H x =/= 0h <-> E. y e. H ( normh ` y ) = 1 )

  proof
    vx
    cv
    #
    c0v
    wne
    #
    vx
    cH
    wrex
    vz
    cv
    #
    c0v
    wne
    #
    vz
    cH
    wrex
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    vy
    cH
    wrex
    #
    @1
    @3
    vx
    vz
    cH
    @0
    @2
    c0v
    neeq1
    cbvrexv
    @4
    @8
    @3
    @8
    vz
    cH
    @2
    cH
    wcel
    #
    @3
    wa
    #
    c1
    @2
    cno
    cfv
    #
    cdiv
    co
    #
    @2
    csm
    co
    #
    cH
    wcel
    #
    @13
    cno
    cfv
    #
    c1
    wceq
    #
    @8
    @10
    @12
    cc
    wcel
    #
    @9
    @14
    @10
    @12
    @10
    @11
    @9
    @11
    cr
    wcel
    #
    @3
    @9
    @2
    chil
    wcel
    #
    @18
    @2
    cH
    norm1ex.1
    sheli
    #
    @2
    normcl
    syl
    adantr
    @9
    @11
    cc0
    wne
    #
    @3
    @9
    @19
    @21
    @3
    wb
    @20
    @2
    normne0
    syl
    biimpar
    rereccld
    recnd
    @9
    @3
    simpl
    cH
    csh
    wcel
    @17
    @9
    @14
    norm1ex.1
    @12
    @2
    cH
    shmulcl
    mp3an1
    syl2anc
    @9
    @19
    @3
    @16
    @20
    @2
    norm1
    sylan
    @7
    @16
    vy
    @13
    cH
    @5
    @13
    wceq
    @6
    @15
    c1
    @5
    @13
    cno
    fveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimiva
    @8
    @5
    c0v
    wne
    #
    vy
    cH
    wrex
    @4
    @7
    @22
    vy
    cH
    @7
    @6
    cc0
    wceq
    #
    wn
    @5
    cH
    wcel
    #
    @22
    @7
    @23
    c1
    cc0
    wceq
    c1
    cc0
    ax-1ne0
    neii
    @6
    c1
    cc0
    eqeq1
    mtbiri
    @24
    @23
    @5
    c0v
    @24
    @5
    chil
    wcel
    @23
    @5
    c0v
    wceq
    wb
    @5
    cH
    norm1ex.1
    sheli
    @5
    norm-i
    syl
    necon3bbid
    syl5ib
    reximia
    @22
    @3
    vy
    vz
    cH
    @5
    @2
    c0v
    neeq1
    cbvrexv
    sylib
    impbii
    bitri
end
