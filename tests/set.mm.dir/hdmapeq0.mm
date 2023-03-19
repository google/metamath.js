include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "clspn.mm"
include "cmpd.mm"
include "eqid.mm"
include "hdmap10.mm"
include "mapd0.mm"
include "eqeq12d.mm"
include "clss.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsssn0.mm"
include "syl.mm"
include "mapd11.mm"
include "cbs.mm"
include "wb.mm"
include "lcdlmod.mm"
include "hdmapcl.mm"
include "lspsneq0.mm"
include "3bitr3rd.mm"
include "bitrd.mm"

theorem hdmapeq0
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume hdmap12a.h: |- H = ( LHyp ` K )
  assume hdmap12a.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap12a.v: |- V = ( Base ` U )
  assume hdmap12a.o: |- .0. = ( 0g ` U )
  assume hdmap12a.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap12a.q: |- Q = ( 0g ` C )
  assume hdmap12a.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap12a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap12a.x: |- ( ph -> T e. V )


  assert |- ( ph -> ( ( S ` T ) = Q <-> T = .0. ) )

  proof
    wph
    cT
    cS
    cfv
    #
    cQ
    wceq
    #
    cT
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    c.0
    csn
    #
    wceq
    #
    cT
    c.0
    wceq
    #
    wph
    @3
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cfv
    #
    @4
    @7
    cfv
    #
    wceq
    @0
    csn
    cC
    clspn
    cfv
    #
    cfv
    #
    cQ
    csn
    #
    wceq
    #
    @5
    @1
    wph
    @8
    @11
    @9
    @12
    wph
    cC
    cS
    cT
    cU
    cH
    cK
    @10
    @7
    @2
    cV
    cW
    hdmap12a.h
    hdmap12a.u
    hdmap12a.v
    @2
    eqid
    #
    hdmap12a.c
    @10
    eqid
    #
    @7
    eqid
    #
    hdmap12a.s
    hdmap12a.k
    hdmap12a.x
    hdmap10
    wph
    cC
    cU
    cH
    cK
    @7
    c.0
    cW
    cQ
    hdmap12a.h
    @16
    hdmap12a.u
    hdmap12a.o
    hdmap12a.c
    hdmap12a.q
    hdmap12a.k
    mapd0
    eqeq12d
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    @7
    cW
    @3
    @4
    hdmap12a.h
    hdmap12a.u
    @17
    eqid
    #
    @16
    hdmap12a.k
    wph
    cU
    clmod
    wcel
    #
    cT
    cV
    wcel
    #
    @3
    @17
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap12a.h
    hdmap12a.u
    hdmap12a.k
    dvhlmod
    #
    hdmap12a.x
    @17
    @2
    cV
    cU
    cT
    hdmap12a.v
    @18
    @14
    lspsncl
    syl2anc
    wph
    @19
    @4
    @17
    wcel
    @21
    @17
    cU
    c.0
    hdmap12a.o
    @18
    lsssn0
    syl
    mapd11
    wph
    cC
    clmod
    wcel
    @0
    cC
    cbs
    cfv
    #
    wcel
    @13
    @1
    wb
    wph
    cC
    cH
    cK
    cW
    hdmap12a.h
    hdmap12a.c
    hdmap12a.k
    lcdlmod
    wph
    cC
    @22
    cS
    cT
    cU
    cH
    cK
    cV
    cW
    hdmap12a.h
    hdmap12a.u
    hdmap12a.v
    hdmap12a.c
    @22
    eqid
    #
    hdmap12a.s
    hdmap12a.k
    hdmap12a.x
    hdmapcl
    @10
    @22
    cC
    @0
    cQ
    @23
    hdmap12a.q
    @15
    lspsneq0
    syl2anc
    3bitr3rd
    wph
    @19
    @20
    @5
    @6
    wb
    @21
    hdmap12a.x
    @2
    cV
    cU
    cT
    c.0
    hdmap12a.v
    hdmap12a.o
    @14
    lspsneq0
    syl2anc
    bitrd
end
