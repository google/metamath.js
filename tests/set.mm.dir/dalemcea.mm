include "co.mm"
include "cmee.mm"
include "cfv.mm"
include "cops.mm"
include "wcel.mm"
include "cbs.mm"
include "cp0.mm"
include "wne.mm"
include "wbr.mm"
include "wceq.mm"
include "dalemkeop.mm"
include "dalemceb.mm"
include "chlt.mm"
include "clln.mm"
include "dalemkehl.mm"
include "dalempjsen.mm"
include "dalemqea.mm"
include "dalemtea.mm"
include "dalemqnet.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "dalem1.mm"
include "cplt.mm"
include "wn.mm"
include "dalem-clpjq.mm"
include "dalempjqeb.mm"
include "op0le.mm"
include "syl2anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "wb.mm"
include "opltn0.mm"
include "mpbird.mm"
include "dalemclpjs.mm"
include "dalemclqjt.mm"
include "clat.mm"
include "wa.mm"
include "dalemkelat.mm"
include "dalempea.mm"
include "dalemsea.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cpo.mm"
include "wi.mm"
include "opposet.mm"
include "syl.mm"
include "op0cl.mm"
include "latmcl.mm"
include "pltletr.mm"
include "mp2and.mm"
include "mpbid.mm"
include "2llnmat.mm"
include "syl32anc.mm"
include "leat2.mm"
include "eqeltrd.mm"

theorem dalemcea
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem1.o: |- O = ( LPlanes ` K )
  assume dalem1.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ph -> C e. A )

  proof
    wph
    cC
    cP
    cS
    c.or
    co
    #
    cQ
    cT
    c.or
    co
    #
    cK
    cmee
    cfv
    #
    co
    #
    cA
    wph
    cK
    cops
    wcel
    #
    cC
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    cA
    wcel
    #
    cC
    cK
    cp0
    cfv
    #
    wne
    #
    cC
    @3
    c.le
    wbr
    #
    cC
    @3
    wceq
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemkeop
    #
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemc.a
    dalemceb
    #
    wph
    cK
    chlt
    wcel
    #
    @0
    cK
    clln
    cfv
    #
    wcel
    @1
    @14
    wcel
    #
    @0
    @1
    wne
    @3
    @8
    wne
    #
    @7
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemkehl
    #
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem1.o
    dalem1.y
    dalempjsen
    wph
    @13
    cQ
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cQ
    cT
    wne
    @15
    @17
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemqea
    #
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemtea
    #
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem1.o
    dalem1.y
    dalemqnet
    cA
    cQ
    cT
    c.or
    cK
    @14
    dalemc.j
    dalemc.a
    @14
    eqid
    #
    llni2
    syl31anc
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem1.o
    dalem1.y
    dalem1
    wph
    @8
    @3
    cK
    cplt
    cfv
    #
    wbr
    #
    @16
    wph
    @8
    cC
    @23
    wbr
    #
    @10
    @24
    wph
    @25
    @9
    wph
    cC
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @9
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalem-clpjq
    wph
    @27
    cC
    @8
    wph
    @27
    cC
    @8
    wceq
    @8
    @26
    c.le
    wbr
    #
    wph
    @4
    @26
    @5
    wcel
    @28
    @11
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemc.j
    dalemc.a
    dalempjqeb
    @5
    cK
    c.le
    @26
    @8
    @5
    eqid
    #
    dalemc.l
    @8
    eqid
    #
    op0le
    syl2anc
    cC
    @8
    @26
    c.le
    breq1
    syl5ibrcom
    necon3bd
    mpd
    #
    wph
    @4
    @6
    @25
    @9
    wb
    @11
    @12
    @5
    @23
    cK
    cC
    @8
    @29
    @23
    eqid
    #
    @30
    opltn0
    syl2anc
    mpbird
    wph
    cC
    @0
    c.le
    wbr
    #
    cC
    @1
    c.le
    wbr
    #
    @10
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemclpjs
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemclqjt
    wph
    cK
    clat
    wcel
    #
    @6
    @0
    @5
    wcel
    #
    @1
    @5
    wcel
    #
    @33
    @34
    wa
    @10
    wb
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemkelat
    #
    @12
    wph
    @13
    cP
    cA
    wcel
    cS
    cA
    wcel
    @36
    @17
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalempea
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalema.ph
    dalemsea
    cA
    @5
    c.or
    cK
    cP
    cS
    @29
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    #
    wph
    @13
    @18
    @19
    @37
    @17
    @20
    @21
    cA
    @5
    c.or
    cK
    cQ
    cT
    @29
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    #
    @5
    cK
    c.le
    @2
    cC
    @0
    @1
    @29
    dalemc.l
    @2
    eqid
    #
    latlem12
    syl13anc
    mpbi2and
    #
    wph
    cK
    cpo
    wcel
    #
    @8
    @5
    wcel
    #
    @6
    @3
    @5
    wcel
    #
    @25
    @10
    wa
    @24
    wi
    wph
    @4
    @43
    @11
    cK
    opposet
    syl
    wph
    @4
    @44
    @11
    @5
    cK
    @8
    @29
    @30
    op0cl
    syl
    @12
    wph
    @35
    @36
    @37
    @45
    @38
    @39
    @40
    @5
    cK
    @2
    @0
    @1
    @29
    @41
    latmcl
    syl3anc
    #
    @5
    @23
    cK
    c.le
    @8
    cC
    @3
    @29
    dalemc.l
    @32
    pltletr
    syl13anc
    mp2and
    wph
    @4
    @45
    @24
    @16
    wb
    @11
    @46
    @5
    @23
    cK
    @3
    @8
    @29
    @32
    @30
    opltn0
    syl2anc
    mpbid
    cA
    cK
    @2
    @14
    @0
    @1
    @8
    @41
    @30
    dalemc.a
    @22
    2llnmat
    syl32anc
    #
    @31
    @42
    cA
    @5
    @3
    cK
    c.le
    cC
    @8
    @29
    dalemc.l
    @30
    dalemc.a
    leat2
    syl32anc
    @47
    eqeltrd
end
