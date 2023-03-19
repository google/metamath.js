include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "coc.mm"
include "cfv.mm"
include "cjn.mm"
include "wceq.mm"
include "simpl.mm"
include "clat.mm"
include "ollat.mm"
include "adantr.mm"
include "cops.mm"
include "olop.mm"
include "simpr1.mm"
include "eqid.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "oldmj3.mm"
include "latjass.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "oldmj4.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "3eqtr3rd.mm"
include "oldmj2.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem latmassOLD
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) ./\ Z ) = ( X ./\ ( Y ./\ Z ) ) )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    cZ
    c.an
    co
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cY
    @8
    cfv
    #
    cZ
    @8
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    @12
    co
    #
    @8
    cfv
    #
    cX
    @13
    @8
    cfv
    #
    c.an
    co
    #
    cX
    cY
    cZ
    c.an
    co
    #
    c.an
    co
    @5
    @9
    @10
    @12
    co
    #
    @11
    @12
    co
    #
    @8
    cfv
    #
    @19
    @8
    cfv
    #
    cZ
    c.an
    co
    #
    @15
    @7
    @5
    @0
    @19
    cB
    wcel
    #
    @3
    @21
    @23
    wceq
    @0
    @4
    simpl
    #
    @5
    cK
    clat
    wcel
    #
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @24
    @0
    @26
    @4
    cK
    ollat
    adantr
    #
    @5
    cK
    cops
    wcel
    #
    @1
    @27
    @0
    @30
    @4
    cK
    olop
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cB
    cK
    @8
    cX
    olmass.b
    @8
    eqid
    #
    opoccl
    syl2anc
    #
    @5
    @30
    @2
    @28
    @31
    @0
    @1
    @2
    @3
    simpr2
    cB
    cK
    @8
    cY
    olmass.b
    @33
    opoccl
    syl2anc
    #
    cB
    @12
    cK
    @9
    @10
    olmass.b
    @12
    eqid
    #
    latjcl
    syl3anc
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    @12
    cK
    c.an
    @8
    @19
    cZ
    olmass.b
    @36
    olmass.m
    @33
    oldmj3
    syl3anc
    @5
    @20
    @14
    @8
    @5
    @26
    @27
    @28
    @11
    cB
    wcel
    #
    @20
    @14
    wceq
    @29
    @34
    @35
    @5
    @30
    @3
    @38
    @31
    @37
    cB
    cK
    @8
    cZ
    olmass.b
    @33
    opoccl
    syl2anc
    #
    cB
    @12
    cK
    @9
    @10
    @11
    olmass.b
    @36
    latjass
    syl13anc
    fveq2d
    @5
    @22
    @6
    cZ
    c.an
    @0
    @1
    @2
    @22
    @6
    wceq
    @3
    cB
    @12
    cK
    c.an
    @8
    cX
    cY
    olmass.b
    @36
    olmass.m
    @33
    oldmj4
    3adant3r3
    oveq1d
    3eqtr3rd
    @5
    @0
    @1
    @13
    cB
    wcel
    #
    @15
    @17
    wceq
    @25
    @32
    @5
    @26
    @28
    @38
    @40
    @29
    @35
    @39
    cB
    @12
    cK
    @10
    @11
    olmass.b
    @36
    latjcl
    syl3anc
    cB
    @12
    cK
    c.an
    @8
    cX
    @13
    olmass.b
    @36
    olmass.m
    @33
    oldmj2
    syl3anc
    @5
    @16
    @18
    cX
    c.an
    @0
    @2
    @3
    @16
    @18
    wceq
    @1
    cB
    @12
    cK
    c.an
    @8
    cY
    cZ
    olmass.b
    @36
    olmass.m
    @33
    oldmj4
    3adant3r1
    oveq2d
    3eqtrd
end
