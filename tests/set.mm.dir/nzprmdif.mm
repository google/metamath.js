include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "cdif.mm"
include "clcm.mm"
include "co.mm"
include "cmul.mm"
include "cin.mm"
include "difin.mm"
include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "prmz.mm"
include "syl.mm"
include "nzin.mm"
include "difeq2d.mm"
include "syl5eqr.mm"
include "cgcd.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "lcmgcd.mm"
include "syl2anc.mm"
include "c1.mm"
include "wne.mm"
include "wb.mm"
include "prmrp.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "cn0.mm"
include "lcmcl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "zred.mm"
include "remulcld.mm"
include "cn.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "mulge0d.mm"
include "absidd.mm"
include "3eqtr3d.mm"
include "sneqd.mm"
include "imaeq2d.mm"

theorem nzprmdif
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume nzprmdif.m: |- ( ph -> M e. Prime )
  assume nzprmdif.n: |- ( ph -> N e. Prime )
  assume nzprmdif.ne: |- ( ph -> M =/= N )


  assert |- ( ph -> ( ( || " { M } ) \ ( || " { N } ) ) = ( ( || " { M } ) \ ( || " { ( M x. N ) } ) ) )

  proof
    wph
    cdvds
    cM
    csn
    cima
    #
    cdvds
    cN
    csn
    cima
    #
    cdif
    #
    @0
    cdvds
    cM
    cN
    clcm
    co
    #
    csn
    #
    cima
    #
    cdif
    #
    @0
    cdvds
    cM
    cN
    cmul
    co
    #
    csn
    #
    cima
    #
    cdif
    wph
    @2
    @0
    @0
    @1
    cin
    #
    cdif
    @6
    @0
    @1
    difin
    wph
    @10
    @5
    @0
    wph
    cM
    cN
    wph
    cM
    cprime
    wcel
    #
    cM
    cz
    wcel
    #
    nzprmdif.m
    cM
    prmz
    syl
    #
    wph
    cN
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    nzprmdif.n
    cN
    prmz
    syl
    #
    nzin
    difeq2d
    syl5eqr
    wph
    @5
    @9
    @0
    wph
    @4
    @8
    cdvds
    wph
    @3
    @7
    wph
    @3
    cM
    cN
    cgcd
    co
    #
    cmul
    co
    #
    @7
    cabs
    cfv
    #
    @3
    @7
    wph
    @12
    @15
    @18
    @19
    wceq
    @13
    @16
    cM
    cN
    lcmgcd
    syl2anc
    wph
    @18
    @3
    c1
    cmul
    co
    @3
    wph
    @17
    c1
    @3
    cmul
    wph
    @17
    c1
    wceq
    #
    cM
    cN
    wne
    #
    nzprmdif.ne
    wph
    @11
    @14
    @20
    @21
    wb
    nzprmdif.m
    nzprmdif.n
    cM
    cN
    prmrp
    syl2anc
    mpbird
    oveq2d
    wph
    @3
    wph
    @3
    wph
    @12
    @15
    @3
    cn0
    wcel
    @13
    @16
    cM
    cN
    lcmcl
    syl2anc
    nn0cnd
    mulid1d
    eqtrd
    wph
    @7
    wph
    cM
    cN
    wph
    cM
    @13
    zred
    #
    wph
    cN
    @16
    zred
    #
    remulcld
    wph
    cM
    cN
    @22
    @23
    wph
    cM
    wph
    cM
    wph
    @11
    cM
    cn
    wcel
    nzprmdif.m
    cM
    prmnn
    syl
    nnnn0d
    nn0ge0d
    wph
    cN
    wph
    cN
    wph
    @14
    cN
    cn
    wcel
    nzprmdif.n
    cN
    prmnn
    syl
    nnnn0d
    nn0ge0d
    mulge0d
    absidd
    3eqtr3d
    sneqd
    imaeq2d
    difeq2d
    eqtrd
end
