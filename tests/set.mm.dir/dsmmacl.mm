include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "eqid.mm"
include "wa.mm"
include "cdsmm.mm"
include "cmnd.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "dsmmelbas.mm"
include "mpbid.mm"
include "simpld.mm"
include "prdsplusgcl.mm"
include "cplusg.mm"
include "adantr.mm"
include "simpr.mm"
include "prdsplusgfval.mm"
include "neeq1d.mm"
include "rabbidva.mm"
include "cun.mm"
include "wss.mm"
include "simprd.mm"
include "unfi.mm"
include "syl2anc.mm"
include "wo.mm"
include "wn.mm"
include "wceq.mm"
include "neorian.mm"
include "bicomi.mm"
include "con1bii.mm"
include "ffvelrnda.mm"
include "mndidcl.mm"
include "mndlid.mm"
include "oveq12.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "necon1ad.mm"
include "ss2rabdv.mm"
include "unrab.mm"
include "syl6sseqr.mm"
include "ssfi.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"

theorem dsmmacl
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let va: setvar a
  let c.0: class .0.
  assume dsmmcl.p: |- P = ( S Xs_ R )
  assume dsmmcl.h: |- H = ( Base ` ( S (+)m R ) )
  assume dsmmcl.i: |- ( ph -> I e. W )
  assume dsmmcl.s: |- ( ph -> S e. V )
  assume dsmmcl.r: |- ( ph -> R : I --> Mnd )
  assume dsmmacl.j: |- ( ph -> J e. H )
  assume dsmmacl.k: |- ( ph -> K e. H )
  assume dsmmacl.a: |- .+ = ( +g ` P )


  assert |- ( ph -> ( J .+ K ) e. H )

  proof
    wph
    cJ
    cK
    c.pl
    co
    #
    cH
    wcel
    @0
    cP
    cbs
    cfv
    #
    wcel
    va
    cv
    #
    @0
    cfv
    #
    @2
    cR
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    va
    cI
    crab
    #
    cfn
    wcel
    wph
    @1
    c.pl
    cR
    cS
    cJ
    cK
    cI
    cV
    cW
    cP
    dsmmcl.p
    @1
    eqid
    #
    dsmmacl.a
    dsmmcl.s
    dsmmcl.i
    dsmmcl.r
    wph
    cJ
    @1
    wcel
    #
    @2
    cJ
    cfv
    #
    @5
    wne
    #
    va
    cI
    crab
    #
    cfn
    wcel
    #
    wph
    cJ
    cH
    wcel
    @9
    @13
    wa
    dsmmacl.j
    wph
    @1
    cS
    cR
    cdsmm
    co
    #
    cP
    cR
    cS
    cH
    cI
    cW
    cJ
    va
    dsmmcl.p
    @14
    eqid
    #
    @8
    dsmmcl.h
    dsmmcl.i
    wph
    cI
    cmnd
    cR
    wf
    cR
    cI
    wfn
    #
    dsmmcl.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    dsmmelbas
    mpbid
    #
    simpld
    #
    wph
    cK
    @1
    wcel
    #
    @2
    cK
    cfv
    #
    @5
    wne
    #
    va
    cI
    crab
    #
    cfn
    wcel
    #
    wph
    cK
    cH
    wcel
    @20
    @24
    wa
    dsmmacl.k
    wph
    @1
    @14
    cP
    cR
    cS
    cH
    cI
    cW
    cK
    va
    dsmmcl.p
    @15
    @8
    dsmmcl.h
    dsmmcl.i
    @17
    dsmmelbas
    mpbid
    #
    simpld
    #
    prdsplusgcl
    wph
    @7
    @10
    @21
    @4
    cplusg
    cfv
    #
    co
    #
    @5
    wne
    #
    va
    cI
    crab
    #
    cfn
    wph
    @6
    @29
    va
    cI
    wph
    @2
    cI
    wcel
    #
    wa
    #
    @3
    @28
    @5
    @32
    @1
    c.pl
    cR
    cS
    cJ
    cK
    cI
    @2
    cV
    cW
    cP
    dsmmcl.p
    @8
    wph
    cS
    cV
    wcel
    @31
    dsmmcl.s
    adantr
    wph
    cI
    cW
    wcel
    @31
    dsmmcl.i
    adantr
    wph
    @16
    @31
    @17
    adantr
    wph
    @9
    @31
    @19
    adantr
    wph
    @20
    @31
    @26
    adantr
    dsmmacl.a
    wph
    @31
    simpr
    prdsplusgfval
    neeq1d
    rabbidva
    wph
    @12
    @23
    cun
    #
    cfn
    wcel
    #
    @30
    @33
    wss
    @30
    cfn
    wcel
    wph
    @13
    @24
    @34
    wph
    @9
    @13
    @18
    simprd
    wph
    @20
    @24
    @25
    simprd
    @12
    @23
    unfi
    syl2anc
    wph
    @30
    @11
    @22
    wo
    #
    va
    cI
    crab
    @33
    wph
    @29
    @35
    va
    cI
    @32
    @35
    @28
    @5
    @35
    wn
    @10
    @5
    wceq
    @21
    @5
    wceq
    wa
    #
    @32
    @28
    @5
    wceq
    #
    @36
    @35
    @35
    @36
    wn
    @10
    @5
    @21
    @5
    neorian
    bicomi
    con1bii
    @32
    @37
    @36
    @5
    @5
    @27
    co
    #
    @5
    wceq
    #
    @32
    @4
    cmnd
    wcel
    #
    @5
    @4
    cbs
    cfv
    #
    wcel
    #
    @39
    wph
    cI
    cmnd
    @2
    cR
    dsmmcl.r
    ffvelrnda
    #
    @32
    @40
    @42
    @43
    @41
    @4
    @5
    @41
    eqid
    #
    @5
    eqid
    #
    mndidcl
    syl
    @41
    @27
    @4
    @5
    @5
    @44
    @27
    eqid
    @45
    mndlid
    syl2anc
    @36
    @28
    @38
    @5
    @10
    @5
    @21
    @5
    @27
    oveq12
    eqeq1d
    syl5ibrcom
    syl5bi
    necon1ad
    ss2rabdv
    @11
    @22
    va
    cI
    unrab
    syl6sseqr
    @33
    @30
    ssfi
    syl2anc
    eqeltrd
    wph
    @1
    @14
    cP
    cR
    cS
    cH
    cI
    cW
    @0
    va
    dsmmcl.p
    @15
    @8
    dsmmcl.h
    dsmmcl.i
    @17
    dsmmelbas
    mpbir2and
end
