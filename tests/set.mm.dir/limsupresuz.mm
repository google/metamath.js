include "cres.mm"
include "cr.mm"
include "clsp.mm"
include "cfv.mm"
include "wceq.mm"
include "rescom.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "relres.mm"
include "relssres.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "reseq1d.mm"
include "resres.mm"
include "uzinico.mm"
include "reseq2d.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "cvv.mm"
include "zred.mm"
include "eqid.mm"
include "resexd.mm"
include "limsupresico.mm"
include "eqtrd.mm"
include "limsupresre.mm"
include "3eqtr3d.mm"

theorem limsupresuz
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume limsupresuz.m: |- ( ph -> M e. ZZ )
  assume limsupresuz.z: |- Z = ( ZZ>= ` M )
  assume limsupresuz.f: |- ( ph -> F e. V )
  assume limsupresuz.d: |- ( ph -> dom ( F |` RR ) C_ ZZ )


  assert |- ( ph -> ( limsup ` ( F |` Z ) ) = ( limsup ` F ) )

  proof
    wph
    cF
    cZ
    cres
    #
    cr
    cres
    #
    clsp
    cfv
    #
    cF
    cr
    cres
    #
    clsp
    cfv
    #
    @0
    clsp
    cfv
    cF
    clsp
    cfv
    wph
    @2
    @3
    cZ
    cres
    #
    clsp
    cfv
    #
    @4
    @2
    @6
    wceq
    wph
    @1
    @5
    clsp
    cF
    cZ
    cr
    rescom
    fveq2i
    a1i
    wph
    @6
    @3
    cM
    cpnf
    cico
    co
    #
    cres
    #
    clsp
    cfv
    @4
    wph
    @5
    @8
    clsp
    wph
    @8
    @3
    cz
    cres
    #
    @7
    cres
    #
    @3
    cz
    @7
    cin
    #
    cres
    #
    @5
    wph
    @3
    @9
    @7
    wph
    @9
    @3
    wph
    @3
    wrel
    #
    @3
    cdm
    cz
    wss
    @9
    @3
    wceq
    @13
    wph
    cF
    cr
    relres
    a1i
    limsupresuz.d
    @3
    cz
    relssres
    syl2anc
    eqcomd
    reseq1d
    @10
    @12
    wceq
    wph
    @3
    cz
    @7
    resres
    a1i
    wph
    @11
    cZ
    @3
    wph
    cZ
    @11
    wph
    cM
    cZ
    limsupresuz.m
    limsupresuz.z
    uzinico
    eqcomd
    reseq2d
    3eqtrrd
    fveq2d
    wph
    @3
    cM
    cvv
    @7
    wph
    cM
    limsupresuz.m
    zred
    @7
    eqid
    wph
    cF
    cr
    cV
    limsupresuz.f
    resexd
    limsupresico
    eqtrd
    eqtrd
    wph
    @0
    cvv
    wph
    cF
    cZ
    cV
    limsupresuz.f
    resexd
    limsupresre
    wph
    cF
    cV
    limsupresuz.f
    limsupresre
    3eqtr3d
end
