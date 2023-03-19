include "crrh.mm"
include "cfv.mm"
include "cqqh.mm"
include "ccnext.mm"
include "co.mm"
include "ccn.mm"
include "ctps.mm"
include "wcel.mm"
include "wceq.mm"
include "cxme.mm"
include "cnrg.mm"
include "cngp.mm"
include "nrgngp.mm"
include "ngpxms.mm"
include "3syl.mm"
include "xmstps.mm"
include "syl.mm"
include "rrhval.mm"
include "cq.mm"
include "crefld.mm"
include "cuss.mm"
include "ccnfld.mm"
include "cress.mm"
include "cr.mm"
include "rebase.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctopn.mm"
include "retopn.mm"
include "eqtri.mm"
include "eqid.mm"
include "df-refld.mm"
include "oveq1i.mm"
include "cvv.mm"
include "wss.mm"
include "reex.mm"
include "qssre.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "fveq2i.mm"
include "ccms.mm"
include "cmt.mm"
include "recms.mm"
include "cmsms.mm"
include "mstps.mm"
include "mp2b.mm"
include "a1i.mm"
include "ccusp.mm"
include "cusp.mm"
include "recusp.mm"
include "cuspusp.mm"
include "mp1i.mm"
include "cmopn.mm"
include "cha.mm"
include "xmstopn.mm"
include "cxmt.mm"
include "xmsxmet.mm"
include "methaus.mm"
include "eqeltrd.mm"
include "cmetu.mm"
include "cucn.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "qqhucn.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "ccl.mm"
include "fveq1i.mm"
include "qdensere.mm"
include "ucnextcn.mm"

theorem rrhcn
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cJ: class J
  let cK: class K
  let cZ: class Z
  assume rrhf.d: |- D = ( ( dist ` R ) |` ( B X. B ) )
  assume rrhf.j: |- J = ( topGen ` ran (,) )
  assume rrhf.b: |- B = ( Base ` R )
  assume rrhf.k: |- K = ( TopOpen ` R )
  assume rrhf.z: |- Z = ( ZMod ` R )
  assume rrhf.1: |- ( ph -> R e. DivRing )
  assume rrhf.2: |- ( ph -> R e. NrmRing )
  assume rrhf.3: |- ( ph -> Z e. NrmMod )
  assume rrhf.4: |- ( ph -> ( chr ` R ) = 0 )
  assume rrhf.5: |- ( ph -> R e. CUnifSp )
  assume rrhf.6: |- ( ph -> ( UnifSt ` R ) = ( metUnif ` D ) )


  assert |- ( ph -> ( RRHom ` R ) e. ( J Cn K ) )

  proof
    wph
    cR
    crrh
    cfv
    #
    cR
    cqqh
    cfv
    #
    cJ
    cK
    ccnext
    co
    cfv
    #
    cJ
    cK
    ccn
    co
    wph
    cR
    ctps
    wcel
    #
    @0
    @2
    wceq
    wph
    cR
    cxme
    wcel
    #
    @3
    wph
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    @4
    rrhf.2
    cR
    nrgngp
    cR
    ngpxms
    3syl
    #
    cR
    xmstps
    syl
    #
    cR
    cJ
    cK
    ctps
    rrhf.j
    rrhf.k
    rrhval
    syl
    wph
    cq
    crefld
    cuss
    cfv
    #
    ccnfld
    cq
    cress
    co
    #
    cuss
    cfv
    #
    cR
    cuss
    cfv
    #
    @1
    cJ
    cK
    crefld
    cR
    cr
    cB
    rebase
    rrhf.b
    cJ
    cioo
    crn
    ctg
    cfv
    #
    crefld
    ctopn
    cfv
    rrhf.j
    retopn
    eqtri
    rrhf.k
    @7
    eqid
    @8
    crefld
    cq
    cress
    co
    #
    cuss
    @12
    ccnfld
    cr
    cress
    co
    #
    cq
    cress
    co
    #
    @8
    crefld
    @13
    cq
    cress
    df-refld
    oveq1i
    cr
    cvv
    wcel
    cq
    cr
    wss
    #
    @14
    @8
    wceq
    reex
    qssre
    cr
    cq
    ccnfld
    cvv
    ressabs
    mp2an
    eqtr2i
    fveq2i
    @10
    eqid
    crefld
    ctps
    wcel
    #
    wph
    crefld
    ccms
    wcel
    crefld
    cmt
    wcel
    @16
    recms
    crefld
    cmsms
    crefld
    mstps
    mp2b
    a1i
    crefld
    ccusp
    wcel
    crefld
    cusp
    wcel
    wph
    recusp
    crefld
    cuspusp
    mp1i
    @6
    rrhf.5
    wph
    cK
    cD
    cmopn
    cfv
    #
    cha
    wph
    @4
    cK
    @17
    wceq
    @5
    cD
    cK
    cR
    cB
    rrhf.k
    rrhf.b
    rrhf.d
    xmstopn
    syl
    wph
    @4
    cD
    cB
    cxmt
    cfv
    wcel
    @17
    cha
    wcel
    @5
    cD
    cR
    cB
    rrhf.b
    rrhf.d
    xmsxmet
    cD
    @17
    cB
    @17
    eqid
    methaus
    3syl
    eqeltrd
    @15
    wph
    qssre
    a1i
    wph
    @1
    @9
    cD
    cmetu
    cfv
    #
    cucn
    co
    @9
    @10
    cucn
    co
    wph
    cB
    @8
    cR
    @9
    @18
    cZ
    rrhf.b
    @8
    eqid
    @9
    eqid
    cD
    cR
    cds
    cfv
    cB
    cB
    cxp
    cres
    cmetu
    rrhf.d
    fveq2i
    rrhf.z
    rrhf.2
    rrhf.1
    rrhf.3
    rrhf.4
    qqhucn
    wph
    @18
    @10
    @9
    cucn
    wph
    @10
    @18
    rrhf.6
    eqcomd
    oveq2d
    eleqtrd
    cq
    cJ
    ccl
    cfv
    #
    cfv
    #
    cr
    wceq
    wph
    @20
    cq
    @11
    ccl
    cfv
    #
    cfv
    cr
    cq
    @19
    @21
    cJ
    @11
    ccl
    rrhf.j
    fveq2i
    fveq1i
    qdensere
    eqtri
    a1i
    ucnextcn
    eqeltrd
end
