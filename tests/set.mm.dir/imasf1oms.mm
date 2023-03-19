include "cxme.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "cmt.mm"
include "msxms.mm"
include "syl.mm"
include "imasf1oxms.mm"
include "wss.mm"
include "eqid.mm"
include "msmet.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "imasf1omet.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "imasbas.mm"
include "eleqtrd.mm"
include "ssid.mm"
include "metres2.mm"
include "sylancl.mm"
include "ctopn.mm"
include "isms.mm"
include "sylanbrc.mm"

theorem imasf1oms
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cD: class D
  let vx: setvar x
  let cE: class E
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  assume imasf1obl.u: |- ( ph -> U = ( F "s R ) )
  assume imasf1obl.v: |- ( ph -> V = ( Base ` R ) )
  assume imasf1obl.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasf1oms.r: |- ( ph -> R e. MetSp )


  assert |- ( ph -> U e. MetSp )

  proof
    wph
    cU
    cxme
    wcel
    cU
    cds
    cfv
    #
    cU
    cbs
    cfv
    #
    @1
    cxp
    cres
    #
    @1
    cme
    cfv
    #
    wcel
    #
    cU
    cmt
    wcel
    wph
    cB
    cR
    cU
    cF
    cV
    imasf1obl.u
    imasf1obl.v
    imasf1obl.f
    wph
    cR
    cmt
    wcel
    #
    cR
    cxme
    wcel
    imasf1oms.r
    cR
    msxms
    syl
    imasf1oxms
    wph
    @0
    @3
    wcel
    @1
    @1
    wss
    @4
    wph
    @0
    cB
    cme
    cfv
    @3
    wph
    cB
    @0
    cR
    cU
    cR
    cds
    cfv
    #
    cV
    cV
    cxp
    #
    cres
    #
    cF
    cV
    cmt
    imasf1obl.u
    imasf1obl.v
    imasf1obl.f
    imasf1oms.r
    @8
    eqid
    @0
    eqid
    wph
    @6
    cR
    cbs
    cfv
    #
    @9
    cxp
    #
    cres
    #
    @9
    cme
    cfv
    #
    @8
    cV
    cme
    cfv
    wph
    @5
    @11
    @12
    wcel
    imasf1oms.r
    @11
    cR
    @9
    @9
    eqid
    @11
    eqid
    msmet
    syl
    wph
    @7
    @10
    @6
    wph
    cV
    @9
    imasf1obl.v
    sqxpeqd
    reseq2d
    wph
    cV
    @9
    cme
    imasf1obl.v
    fveq2d
    3eltr4d
    imasf1omet
    wph
    cB
    @1
    cme
    wph
    cB
    cR
    cU
    cF
    cV
    cmt
    imasf1obl.u
    imasf1obl.v
    wph
    cV
    cB
    cF
    wf1o
    cV
    cB
    cF
    wfo
    imasf1obl.f
    cV
    cB
    cF
    f1ofo
    syl
    imasf1oms.r
    imasbas
    fveq2d
    eleqtrd
    @1
    ssid
    @0
    @1
    @1
    metres2
    sylancl
    @2
    cU
    ctopn
    cfv
    #
    cU
    @1
    @13
    eqid
    @1
    eqid
    @2
    eqid
    isms
    sylanbrc
end
