include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdveca.mm"
include "cfv.mm"
include "clspn.mm"
include "clmod.mm"
include "cbs.mm"
include "clvec.mm"
include "eqid.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "dvavbase.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "dia1dim2.mm"
include "eleqtrrd.mm"

theorem dia1dimid
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dia1dimid.h: |- H = ( LHyp ` K )
  assume dia1dimid.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia1dimid.r: |- R = ( ( trL ` K ) ` W )
  assume dia1dimid.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> F e. ( I ` ( R ` F ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    cF
    cF
    csn
    cW
    cK
    cdveca
    cfv
    cfv
    #
    clspn
    cfv
    #
    cfv
    #
    cF
    cR
    cfv
    cI
    cfv
    @2
    @3
    clmod
    wcel
    #
    cF
    @3
    cbs
    cfv
    #
    wcel
    #
    cF
    @5
    wcel
    @0
    @6
    @1
    @0
    @3
    clvec
    wcel
    @6
    @3
    cH
    cK
    cW
    dia1dimid.h
    @3
    eqid
    #
    dvalvec
    @3
    lveclmod
    syl
    adantr
    @0
    @8
    @1
    @0
    @7
    cT
    cF
    cT
    @3
    cH
    cK
    @7
    cW
    chlt
    dia1dimid.h
    dia1dimid.t
    @9
    @7
    eqid
    #
    dvavbase
    eleq2d
    biimpar
    @4
    @7
    @3
    cF
    @10
    @4
    eqid
    #
    lspsnid
    syl2anc
    cR
    cT
    @3
    cF
    cH
    cI
    cK
    @4
    cW
    dia1dimid.h
    dia1dimid.t
    dia1dimid.r
    @9
    dia1dimid.i
    @11
    dia1dim2
    eleqtrrd
end
