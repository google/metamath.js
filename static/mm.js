const {
  descent: { parse, process },
  metamath: { MM },
} = module;

class Code extends React.Component {
  render() {
    const c = this.props.mm.labels["$c"].map(([, c]) => c).flat();

    if (!this.props.src || this.props.src == "") {
      return <code style={{ padding: "0.3em 0.5em" }}></code>;
    }

    return (
      <code style={{ padding: "0.3em 0.5em" }}>
        {this.props.src.split(" ").map((ch, i) =>
          c.includes(ch) ? (
            <b
              style={{ color: "#7928a1", padding: "0.2em", cursor: "pointer" }}
              title={`${ch} is a declared constant.`}
              key={i}
            >
              {ch}
            </b>
          ) : (
            <span
              key={i}
              style={{ color: "#d91e18", padding: "0.2em", cursor: "pointer" }}
              title={`${ch} is a declared var.`}
            >
              {ch}
            </span>
          )
        )}
      </code>
    );
  }
}

class Theorem extends React.Component {
  render() {
    const mm = this.props.mm;
    const statement = mm.labels[this.props.label];
    let [
      a,
      [d = [], args = [], hyp = [], [type = "", theorem = []] = []],
      verifier = () => [],
      proof = [],
    ] = statement;

    let steps = [];

    if (this.props.loaded) {
      steps = verifier();
    } else if (proof.decompress) {
      steps = proof.decompress().map((step) => [step]);
    } else {
      steps = proof.map((step) => [step]);
    }

    return (
      <div>
        {false && (
          <h1>
            {a == "$a" ? "Axiom" : "Theorem"} "{this.props.label}"
          </h1>
        )}

        {!statement && (
          <div>
            <img src="/static/loading.gif"></img>
          </div>
        )}

        {theorem.length > 0 && (
          <div>
            <h2>Assertion</h2>
            <table>
              <thead>
                <tr>
                  <th>Type</th>
                  <th>Assertion</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td>
                    <Code mm={mm} src={type} />
                  </td>
                  <td>
                    <Code mm={mm} src={theorem.join(" ")} />
                  </td>
                </tr>
              </tbody>
            </table>
          </div>
        )}

        {hyp.length > 0 && (
          <div>
            <h2>Assumptions</h2>
            <table>
              <thead>
                <tr>
                  <th>Label</th>
                  <th>Type</th>
                  <th>Condition</th>
                </tr>
              </thead>
              <tbody>
                {hyp.map(([sequence, type, label], i) => (
                  <tr key={i}>
                    <td>{label}</td>
                    <td>
                      <Code mm={mm} src={type} />
                    </td>
                    <td>
                      <Code mm={mm} src={sequence.join(" ")} />
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )}

        {args.length > 0 && (
          <div>
            <h2>Arguments</h2>
            <table>
              <thead>
                <tr>
                  <th>Label</th>
                  <th>Type</th>
                  <th>Symbol</th>
                </tr>
              </thead>
              <tbody>
                {args.map(([type, name, label], i) => (
                  <tr key={i}>
                    <td>{label}</td>
                    <td>
                      <Code mm={mm} src={type} />
                    </td>
                    <td>
                      <Code mm={mm} src={name} />
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )}

        {a == "$p" && this.props.loaded && <Proof mm={mm} proof={steps} />}
      </div>
    );
  }
}

class Window extends React.Component {
  render() {
    if (!this.props.open) {
      return null;
    }

    const mm = this.props.mm;

    if (!mm.labels[this.props.open]) {
      return null;
    }

    //const open = this.props.open ? this.props.mm.labels[this.props.open] : undefined;
    const open = mm.labels[this.props.open];
    const style = {
      position: "absolute",
      left: "105%",
      width: "80%",
      borderRadius: "6px",
      padding: "0 1em",
      boxShadow: "0 0 10px rgba(0,0,0,0.3)",
      paddingBottom: "2em",
      bottom: 0,
      overflow: "scroll",
    };
    return (
      <div style={style}>
        {open[0] == "$f" && (
          <React.Fragment>
            <h1>Type Declaration "{this.props.open}"</h1>
            <table>
              <thead>
                <tr>
                  <th>Type</th>
                  <th>Name</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td>
                    <Code mm={mm} src={open[1][0]} />
                  </td>
                  <td>
                    <Code mm={mm} src={open[1][1]} />
                  </td>
                </tr>
              </tbody>
            </table>
          </React.Fragment>
        )}

        {open[0] == "$e" && (
          <React.Fragment>
            <h1>Assumption "{this.props.open}"</h1>
            <table>
              <thead>
                <tr>
                  <th>Type</th>
                  <th>Name</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td>
                    <Code mm={mm} src={open[1][0]} />
                  </td>
                  <td>
                    <Code mm={mm} src={open[1][1].join(" ")} />
                  </td>
                </tr>
              </tbody>
            </table>
          </React.Fragment>
        )}

        {(open[0] == "$a" || open[0] == "$p") && (
          <Theorem mm={mm} label={this.props.open}></Theorem>
        )}
      </div>
    );
  }
}

class Proof extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      step: 0,
    };
  }
  render() {
    const markers = [];
    for (let i = 1; i < this.props.proof.length - 1; i++) {
      if (this.props.proof[i][0] == -1) {
        markers.push(this.props.proof[i - 1]);
      }
    }

    const mm = this.props.mm;
    const proof = this.props.proof;

    const step = this.state.step;

    const style = function (highlight, i, type, match) {
      const base = i < step ? {} : { display: "none" };
      if (pops && !match) {
        base["opacity"] = 0.1;
      }
      if (!highlight) {
        return base;
      }
      if (highlight.includes(i)) {
        return base;
      }
      return Object.assign(base, {
        opacity: 0.1,
        backgroundColor: "none",
      });
    };

    const clone = (obj) => JSON.parse(JSON.stringify(obj));

    const steps = clone(proof.filter(([step]) => step != -1));

    for (let i = 0; i < step; i++) {
      const [label, rule = [], args = []] = steps[i];
      if (typeof label == "number") {
        continue;
      }
      for (let arg of args) {
        steps[arg] = [-1];
      }
    }

    let next = steps[this.state.step];

    let pops = false;
    let marker = false;

    if (next) {
      let name = next[0];

      if (typeof name == "number") {
        marker = next;
        next = markers[next[0]];
      }

      const [, , args] = next;
      const [, [d, f, e]] = mm.labels[next[0]];
      for (let i = 0; i < f.length; i++) {
        steps[args[i]].push(f[i][1]);
        pops = true;
      }
      for (let i = 0; i < e.length; i++) {
        steps[args[f.length + i]].push(e[i][0].join(" "));
        pops = true;
      }
    }

    return (
      <div>
        <h2>Proof</h2>
        <input
          type="range"
          min={0}
          max={steps.length - 1}
          value={this.state.step}
          onChange={(event) => this.setState({ step: event.target.value })}
          style={{
            width: "100%",
            height: "15px",
            borderRadius: "5px",
            background: "#d3d3d3",
            outline: "none",
            opacity: "0.7",
            WebkitTransition: ".2s",
            transition: "opacity .2s",
          }}
        />

        <br />
        <br />

        <button
          disabled={this.state.step <= 0}
          onClick={() => this.setState({ step: step - 1 })}
        >
          Back
        </button>
        <button
          disabled={this.state.step >= steps.length}
          onClick={() => this.setState({ step: step + 1 })}
        >
          Next
        </button>

        <br />

        {(() => {
          if (!next) {
            return null;
          }

          const [t, [d, f, e, [type, rule]]] = mm.labels[next[0]];

          return (
            <div>
              <h2>
                Step {step} : {marker ? `Replay step ${marker[2]}: ` : ""}{" "}
                {t == "$a" ? "Axiom" : "Theorem"} {next[0]}
              </h2>
              <p>
                <Code mm={mm} src={type} />{" "}
                <Code mm={mm} src={rule.join(" ")} />
                {pops && (
                  <span>
                    {" "}
                    = <Code mm={mm} src={next[1][0]} />{" "}
                    <Code mm={mm} src={next[1][1].join(" ")} />
                  </span>
                )}
              </p>
            </div>
          );
        })()}

        <br />

        <div style={{ position: "relative", display: "inline-block" }}>
          <table>
            <colgroup>
              <col />
              <col />
              <col style={{ width: "10em" }} />
              <col style={{ width: "25em" }} />
            </colgroup>
            <thead>
              <tr>
                <th>Step</th>
                <th>Rule</th>
                <th>Type</th>
                <th>Expression</th>
              </tr>
            </thead>
            <tbody>
              {steps.map((step, i) => {
                const [label, rule = [], args = [], match] = step;
                const [type = "", result = []] = rule;
                // console.log(match);
                if (label == -1) {
                  return null;
                } else if (typeof label == "number") {
                  return (
                    <tr
                      key={i}
                      style={style(this.state.highlight, i, type, match)}
                      onMouseEnter={() =>
                        this.setState({ highlight: [args, i] })
                      }
                      onMouseLeave={() =>
                        this.setState({ highlight: undefined })
                      }
                    >
                      <td>{i}</td>
                      <td>#{args}</td>
                      <td>
                        <Code mm={mm} src={type} />
                      </td>
                      <td>
                        <Code mm={mm} src={result.flat().join(" ")} />
                        {match && (
                          <span>
                            {" "}
                            = <Code mm={mm} src={match} />
                          </span>
                        )}
                      </td>
                    </tr>
                  );
                } else {
                  return (
                    <tr
                      key={i}
                      style={style(this.state.highlight, i, type, match)}
                      onMouseEnter={() =>
                        this.setState({ highlight: [...args, i] })
                      }
                      onMouseLeave={() =>
                        this.setState({ highlight: undefined })
                      }
                    >
                      <td>{i}</td>
                      <td>
                        <a
                          href={"#" + label}
                          onClick={() => {
                            this.setState({
                              label: step,
                              highlight: undefined,
                            });
                          }}
                        >
                          {label}
                        </a>
                      </td>
                      <td>
                        <Code mm={mm} src={type} />
                        {false && match && (
                          <span>
                            {" "}
                            = <Code mm={mm} src={match} />
                          </span>
                        )}
                      </td>
                      <td>
                        <Code mm={mm} src={result.flat().join(" ")} />
                        {match && (
                          <span>
                            {" "}
                            = <Code mm={mm} src={match} />
                          </span>
                        )}
                      </td>
                    </tr>
                  );
                }
              })}
            </tbody>
          </table>

          <br />
        </div>
      </div>
    );
  }
}

class Metamath extends React.Component {
  async compute() {
    const label = window.location.hash
      ? window.location.hash.substr(1)
      : this.props.label;
    const response = await fetch(`${this.props.dir}/${label}.mm`);
    const body = await response.text();

    {
      const metamath = await new Compiler().compile(body);
      const mm = process(metamath);
      const [, , verifier, proof] = mm.labels[label];
      this.setState({
        label: label,
        open: false,
        loaded: false,
        mm: mm,
      });
    }

    // return;

    const compiler = new Compiler(this.loader.bind(this));

    const source = await compiler.compile(this.props.dir, `${label}.mm`, true);

    const mm = process(source);

    this.setState({
      label: label,
      open: false,
      loaded: true,
      source: source,
      mm: process(source),
    });

    window.scroll({
      top: 0,
      left: 0,
      behavior: "smooth",
    });
  }

  async componentDidMount() {
    window.addEventListener("hashchange", this.compute.bind(this), false);
    this.compute();
  }

  async loader(file) {
    const response = await fetch(file);
    const body = await response.text();

    const that = this;
    return new Promise((resolve, reject) => {
      // Waits 100 ms arbitrarily to simulate slow
      // networks
      //that.setState({
      //  file: file
      //});
      setTimeout(() => {
        resolve(body);
      });
    });
  }

  render() {
    if (!this.state) {
      return null;
    }

    const statement = this.state.mm.labels[this.state.label];
    const [a] = statement;

    const hash = window.location.hash;
    const mm = this.state.mm;

    return (
      <div className="doc">
        <div className="post">
          <div className="post-title">
            <h1>
              {a == "$p" ? "Theorem" : "Axiom"} {this.state.label}
            </h1>
          </div>
          <div className="post-info">
            <div>metamath</div>
            <div className="post-date">2023</div>
          </div>
          <div className="post-body">
            <Theorem
              mm={mm}
              label={this.state.label}
              loaded={this.state.loaded}
            />
          </div>
        </div>
      </div>
    );
  }
}

const {
  compiler: { Compiler },
  descent: { Verifier },
} = module;

class MetaMath extends HTMLElement {
  // connect component
  async connectedCallback() {
    const dir = this.getAttribute("dir");
    const file = this.getAttribute("file");
    const label = this.getAttribute("label");

    ReactDOM.render(
      <Metamath dir={dir} file={file} label={label}></Metamath>,
      this
    );
  }
}

customElements.define("meta-math", MetaMath);
